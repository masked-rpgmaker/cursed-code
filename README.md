# Desafio: Código Maldito

Vide https://condadobraveheart.com/threads/desafio-codigo-maldito.7958/

## Introdução

A linguagem escolhida foi [Lean 4](https://lean-lang.org/).

Para tornar o código o mais maldito possível, os três paradigmas foram implementados na mesma
linguagem. Os programas estão em arquivos distintos:
- [`MainFunc.lean`](./MainFunc.lean): Implementação puramente funcional. Na prática, como Lean é
    uma linguagem puramente funcional, todas as implementações são puramente funcionais. Essa, em
    particular, evita usar syntax sugar relacionado a estruturas de repetição, e segue uma
    implementação mais padrão de linguagens funcionais, que também permite uma prova de correção
    mais simples (vide teorema `run_passAround_respects_likes` no arquivo).
- [`MainStructured.lean`](./MainStructured.lean): Implementação estruturada. Essa implementação é
  estruturada no sentido de Edsger W. Dijkstra e do teorema de Böhm–Jacopini: o programa é composto
  estritamente por comandos sequenciais, condicionais, e blocos de repetição.
- [`MainOOP.lean`](./MainOOP.lean): Implementação orientada a objetos. A orientação a objetos é
  implementada através de passagem de mensagens, e objetos são opacos (i.e. encapsulamento é
  garantido por construção).

Todas as implementações usam como base as definições básicas dos tipos usados para as crianças e os
brinquedos, e a função de gostos de cada criança.

Essas definições, bem como os teoremas que provam que a função de gostos definida corresponde à 
única função possível obedecendo os axiomas dados no  enunciado do desafio, estão no arquivo 
[`Cursed/Basic.lean`](./Cursed/Basic.lean).

## Compilação/Execução

O projeto usa [Lake][lake] como sistema de construção.

A forma mais fácil de obter uma instalação funcional do Lake é através do [gerenciador de versão do
Lean (elan)][elan]. 

Feito isso, basta executar cada programa com o comando correspondente do Lake:
```sh
lake exe cursed-func
lake exe cursed-structured
lake exe cursed-oop
```

Obs.: A compilação depende da [biblioteca de matemática do Lean (Mathlib)][mathlib], e portanto a 
primeira compilação pode ser relativamente custosa.

[lake]: https://github.com/leanprover/lake
[elan]: https://github.com/leanprover/elan
[mathlib]: https://github.com/leanprover-community/mathlib4
