import array, locale, sys, os

### Estrutura de dados simples para uma proteina.
class Protein:
  """Define uma proteina pelo seu nome e respectiva sequencia.
  Nota: Quando no modo de generalized suffix array o campo suffix_array
  da proteina nao tem uso. No modo em que se cria um suffix array para cada
  proteina fica guardado no campo respectivo uma lista de inteiros ordenados
  lexicograficamente de acordo com os sufixos da sequencia que ai se iniciam"""
  def __init__(self, name, sequence):
    self.name = name
    self.sequence = sequence
    self.suffix_array = ""

### Algoritmos de construcao de suffix arrays.
def gsa(proteins):
  """Gera uma generalized suffix array na forma de uma lista de tuplos
  do tipo (int, int) sendo o primeiro elemento o numero de ordem da 
  proteina e o segundo a posicao onde comeca o sufixo a que o tuplo
  se refere."""
  gsa = []
  i = 0
  for protein in proteins:
    l = range(len(protein.sequence))
    x = [i]*len(protein.sequence)
    gsa.extend(zip(x, l))
    i += 1
  gsa.sort(key = lambda e: proteins[e[0]].sequence[e[1]:])
  return gsa

def sa(proteins):
  """Gera uma suffix array para cada proteina que consiste numa lista
  de inteiros onde cada inteiro corresponde ao sufixo que se inicia nessa
  posicao."""
  if not proteins[0].suffix_array:
    for protein in proteins:
      protein.suffix_array = range(len(protein.sequence))
      protein.suffix_array.sort(key=lambda x: buffer(protein.sequence, x))


### Algoritmos de online search
def pof(s, p):
  """Leva a cabo uma pesquisa online utilizando uma versao modificada
  do algoritmo de Boyer-Moore incorporando as ideias de Sunday e de
  Horspool.
  O algoritmo aqui apresentado consiste numa versao simplificada da
  implementacao em C da primitiva find do python (http://bit.ly/tsiBL0)
  e foi originalmente descrito pelo Fredrik Lundh (Google).
  """
  def delta1(x):
    """Versao normal da funcao que gera a tabela delta1 do algoritmo
    de Boyer-Moore que basicamente para cada caracter do padrao computa
    a distancia entre o ultimo caracter e a ocorrencia mais a direita do
    caracter em causa"""
    map = { }
    for i in xrange(len(x)-1, -1, -1):
      c = x[i]
      if c not in map:
        map[c] = abs(i-len(x))
    return map

  n = len(s)
  m = len(p)
  skip = delta1(p)[p[m-1]]
  i = 0
  try:
    while i <= n-m:
      if s[i+m-1] == p[m-1]: # (boyer-moore)
        # potencial match
        if s[i:i+m-1] == p[:m-1]:
          yield i
        
        if s[i+m] not in p:
            i = i + m + 1 # (sunday)
        else:
            i = i + skip # (horspool)
      else:
        # saltar...
        if s[i+m] not in p:
          i = i + m + 1 # (sunday)
        else:
          i = i + 1
  except IndexError:
    pass

def kmp(text, pattern):
  """Knuth-Morris-Pratt: Gera uma failure function (array de n+1 posicoes 
  sendo n o tamanho do padrao) e usa a informacao dessa tabela para decidir 
  quantos shifts podem ser feitos sem que se salte nenhuma ocorrencia de 
  pattern em text evitando assim que se reexaminem caracteres ja matched."""
  
  pattern = list(pattern)

  shifts = [1] * (len(pattern) + 1)
  shift = 1
  for pos in xrange(len(pattern)):
    while shift <= pos and pattern[pos] != pattern[pos-shift]:
      shift += shifts[pos-shift]
    shifts[pos+1] = shift
                                                        
  startPos = 0
  matchLen = 0
  for c in text:
    while matchLen == len(pattern) or \
          matchLen >= 0 and pattern[matchLen] != c:
            startPos += shifts[matchLen]
            matchLen -= shifts[matchLen]
    matchLen += 1
    if matchLen == len(pattern):
      yield startPos

def shift_and(text, pattern):
  m = len(pattern)
  r = ~1L
  mask = array.array('l', [~0L] * (locale.CHAR_MAX+1))
  
  for i in xrange(m):
    mask[ord(pattern[i])] &= ~(1L << i)

  for i in xrange(len(text)):
    r |= mask[ord(text[i])]
    r <<= 1

    if (r & (1L << m)) == 0:
      yield i - m + 1

def fuzzy_shift_and(text, pattern, k):
  m = len(pattern)
  r = array.array('l', [~1L] * (k+1))
  mask = array.array('l', [~0L] * (locale.CHAR_MAX+1))

  for i in xrange(m):
    mask[ord(pattern[i])] &= ~(1L << i)

  for i in xrange(len(text)):
    ord1 = r[0]

    r[0] |= mask[ord(text[i])]
    r[0] <<= 1

    for d in xrange(1,k+1):
      tmp = r[d]
      r[d] = ((mask[ord(text[i])] | r[d]) & ord1) << 1
      ord1 = tmp

    if (r[k] & (1L << m)) == 0:
      yield i - m + 1


### Algoritmos de procura binaria sobre suffix array
def bs(protein, pattern):
  """Faz uma procura binaria sobre o suffix array de uma proteina e usa o
  facto de que a partir do momento que seja encontrada um match esta garantido
  que os restantes estejam contiguos no suffix array bastando portanto
  procurar para a esquerda e direita destes ate que deixe de fazer match."""
  
  l = 0
  lp = len(pattern)
  h = len(protein.sequence)
  while l < h:
    m = (l+h)//2
    cs = protein.sequence[protein.suffix_array[m]:]
    if cs[:lp] < pattern:
      l = m+1
    elif cs[:lp] > pattern:
      h = m
    else:
      positions = []
      om = m
      try:
        while protein.sequence[protein.suffix_array[m]:protein.suffix_array[m]+lp] == pattern:
          positions.append(protein.suffix_array[m])
          m += 1
      except IndexError:
        pass
      m = om
      try:
        while protein.sequence[protein.suffix_array[m-1]:protein.suffix_array[m-1]+lp] == pattern:
          positions.append(protein.suffix_array[m-1])
          m -= 1
      except IndexError:
        pass
      
      return positions
  return []

def bsa(proteins, gsa, pattern):
  """Faz uma procura binaria sobre o suffix array generalizado e usa o
  facto de que a partir do momento que seja encontrada um match esta garantido
  que os restantes estejam contiguos no suffix array bastando portanto
  procurar para a esquerda e direita os limites da suffix array entre os quais
  existem matches. Depois de encontrados os limites percorre esse intervalo e
  devolve a lista de matches pela ordem em que aparecem na gsa."""
  
  l = 0
  lp = len(pattern)
  h = len(gsa)
  while l < h:
    m = (l+h)//2
    cs = proteins[gsa[m][0]].sequence[gsa[m][1]:]
    if cs[:lp] < pattern:
      l = m+1
    elif cs[:lp] > pattern:
      h = m
    else:
      positions = []
      i = m
      j = m - 1
      while i < len(gsa) and j >= 0:
        match = False
        if proteins[gsa[i][0]].sequence[gsa[i][1]:gsa[i][1]+lp] == pattern:
          i += 1
          match = True

        if proteins[gsa[j][0]].sequence[gsa[j][1]:gsa[j][1]+lp] == pattern:
          j -= 1
          match = True
        
        if not match:
          break
      
      return [(proteins[gsa[x][0]], gsa[x][1], gsa[x][0]) for x in xrange(j+1, i)]
  return []

def hamming(sa, sb):
  """Calcula a distancia de hamming entre duas strings, i.e.,
  o numero minimo de substituicoes que sao necessarias fazer para transformar
  sa em sb. Se as strings nao tiverem o mesmo tamanho devolve infinito."""
  
  if len(sa) == len(sb):
    return sum(ca is not cb for ca, cb in zip(sa, sb))
  else:
    return float("inf")

def slices(s, k):
  """Divide uma string s em k strings de tamanho identico. As strings
  maiores (se as houverem) aparecerao no inicio da lista"""
  q, r = divmod(len(s), k)
  ps = [min(i, r) + q*i for i in xrange(k+1)]
  return [s[ps[i]:ps[i+1]] for i in xrange(k)]



def parse_proteins(fasta_file):
  """Percorre um ficheiro no formato fasta e retira o nome e sequencia
  de cada proteina encontrada e adiciona-a a lista de proteinas.
  Nota: O custo de adicionar uma nova proteina a lista e O(1) amortizado
  pois o append esta implementado no python de forma a que quando ha a
  necessidade de fazer realloc o tamanho sera 2*(tamanho actual)."""
  
  proteins = []
  lines = []
  name = ""

  for line in fasta_file:
    if line.startswith(">"):
      if name and lines:
        sequence = "".join(lines)
        proteins.append(Protein(name, sequence))
        lines = []
      name = line.split("|", 2)[1]
    else:
      lines.append(line.rstrip())

  if name and lines:
    sequence = "".join(lines)
    proteins.append(Protein(name, sequence))
      
  return proteins


### Funcoes auxiliares
def use_kmp(proteins, pattern):
  for protein in proteins:
    positions = kmp(protein.sequence, pattern)
    for position in positions:
      print " ".join([protein.name, str(position)])

def use_shift_and(proteins, pattern):
  for protein in proteins:
    for pos in shift_and(protein.sequence, pattern):
      if pos is not None:
        print " ".join([protein.name, str(pos)])

def use_fuzzy_shift_and(proteins, pattern, k):
  for protein in proteins:
    for pos in fuzzy_shift_and(protein.sequence, pattern, k):
      if pos is not None:
        print " ".join([protein.name, str(pos)])


def use_pof(proteins, pattern):
  for protein in proteins:
    for pos in pof(protein.sequence, pattern):
      print " ".join([protein.name, str(pos)])

def use_apof(proteins, pattern, k):
  """Usa o algoritmo pof anteriormente descrito e o truque de dividir o
  pattern em k+1 strings e efectua uma procura exacta online por cada
  substring. Se for encontrada compara todo o padrao com o redor da ocorrencia
  para verificar se a distancia de hamming e inferior a k e nesse caso 
  faz match."""

  def find_by_slice():
    for pos in pof(protein.sequence, sl):
      if hamming(protein.sequence[pos-slsz:pos-slsz+lp], pattern) <= k:
        yield " ".join([protein.name, str(pos-slsz)])

  lp = len(pattern)
  matches = []
  s = {}
  for protein in proteins:
    slsz = 0
    for sl in slices(pattern, k+1):
      for match in find_by_slice():
        matches.append(match)
      slsz += len(sl)
  matches = [s.setdefault(m,m) for m in matches if m not in s]  
  for match in matches:
    print match

def use_bs(proteins, pattern):
  if proteins[0].suffix_array:
    for protein in proteins:
      for pos in bs(protein, pattern):
        print " ".join([protein.name, str(pos)])
  else:
    print "Please index database."

def use_abs(proteins, pattern, k):
  """Usa o algoritmo bs anteriormente descrito e o truque de dividir o
  pattern em k+1 strings e efectua uma procura exacta online por cada
  substring. Se for encontrada compara todo o padrao com o redor da ocorrencia
  para verificar se a distancia de hamming e inferior a k e nesse caso 
  faz match."""

  def find_by_slice():
    for pos in bs(protein, sl):
      if hamming(protein.sequence[pos-slsz:pos-slsz+lp], pattern) <= k:
        yield " ".join([protein.name, str(pos-slsz)])

  lp = len(pattern)
  matches = []
  s = {}
  for protein in proteins:
    slsz = 0
    for sl in slices(pattern, k+1):
      for match in find_by_slice():
        matches.append(match)
      slsz += len(sl)
  matches = [s.setdefault(m,m) for m in matches if m not in s]  
  for match in matches:
    print match


def use_bsa(proteins, gsa, pattern):
  if gsa:
    for pos in bsa(proteins, gsa, pattern):
      print " ".join([pos[0].name, str(pos[1])])
  else:
    print "Please index database."

def use_absa(proteins, gsa, pattern, k):
  """Usa o algoritmo anteriormente descrito para procura binaria sobre uma
  generalized suffix array e o truque de dividir o pattern em k+1 strings
  fazendo uma procura exacta por cada uma dessas strings. Na ocorrencia de um
  match verifica se a distancia de hamming entre o pattern e o redor da posicao
  do texto e inferior ou igual a k e nesse caso guarda o numero de ordem da
  proteina e a posicao da ocorrencia.
  No final e feita uma ordenacao por numero de ordem com criterio de desempate
  baseado na posicao da ocorrencia."""

  def find_by_slice():
    for pos in bsa(proteins, gsa, sl):
      if hamming(pos[0].sequence[pos[1]-slsz:pos[1]-slsz+lp], pattern) <= k:
        yield (pos[2], str(pos[1]-slsz))

  if not gsa:
    print "Please index database."
    return

  lp = len(pattern)
  matches = []
  s = {}
  slsz = 0
  for sl in slices(pattern, k+1):
    for prot, pos in find_by_slice():
      matches.append((prot, int(pos)))
    slsz += len(sl)

  matches = [s.setdefault(m,m) for m in matches if m not in s]
  matches.sort()
  
  for match in matches:
    print " ".join([proteins[match[0]].name, str(match[1])])


def parse_input(database_file):
  proteins = parse_proteins(database_file)
  gs = None
  
  while True:
    try:
      line = raw_input()
      line = line.split(' ')
      
      if line[0] == "E":
        #use_shift_and(proteins, line[1]) # procura exacta shift-and
        #use_pof(proteins, line[1]) # procura exacta com boyer-moore modificado
        use_kmp(proteins, line[1]) # procura exacta com knuth-morris-pratt
      elif line[0] == "I":
        gs = gsa(proteins) # suffix array generalizado
        #sa(proteins) # suffix array por proteina
        print "Database indexed."
      elif line[0] == "B":
        use_bsa(proteins, gs, line[1]) # procura binaria generalized suffix array
        #use_bs(proteins, line[1]) # procura binaria em suffix array por proteina
      elif line[0] == "A":
        use_fuzzy_shift_and(proteins, line[2], int(line[1]))
        #use_apof(proteins, line[2], int(line[1])) # procura aproximada com pof
      elif line[0] == "F":
        use_absa(proteins, gs, line[2], int(line[1])) # procura aproximada com bsa
        #use_abs(proteins, line[2], int(line[1])) # procura aproximada com bs
      else:
        pass
    except EOFError:
      sys.exit(0)
    except KeyboardInterrupt:
      sys.exit(0)

if __name__ == '__main__':
  if len(sys.argv) < 2:
    sys.exit("Usage: %s fasta-file" % sys.argv[0])

  if not os.path.exists(sys.argv[1]):
    sys.exit("Oops: Fasta file %s not found." % sys.argv[1])

  parse_input(open(sys.argv[1]))
