<TeXmacs|1.99.3>

<style|generic>

<\body>
  <doc-data|<doc-title|Terms>>

  <\eqnarray*>
    <tformat|<cwith|1|1|3|3|cell-hyphen|n>|<table|<row|<cell|t>|<cell|::=>|<cell|x>>|<row|<cell|>|<cell|<text|\|>>|<cell|\<lambda\>x.e>>|<row|<cell|>|<cell|<text|\|>>|<cell|e
    <hspace|1> e<rsup|<rprime|'>>>>|<row|<cell|>|<cell|<text|\|>>|<cell|let
    x=e in e<rsup|<rprime|'>>>>|<row|<cell|>|<cell|<text|\|>>|<cell|let rec
    x=e in e<rsup|<rprime|'>>>>>>
  </eqnarray*>

  <doc-data|<doc-title|Types>>

  <\eqnarray*>
    <tformat|<table|<row|<cell|\<sigma\>>|<cell|:\<assign\>>|<cell|\<tau\>>>|<row|<cell|>|<cell|<text|\|>>|<cell|\<forall\>\<alpha\>.
    \<sigma\>>>|<row|<cell|>|<cell|>|<cell|>>|<row|<cell|\<tau\>>|<cell|\<colons\>=>|<cell|\<alpha\>>>|<row|<cell|>|<cell|<text|\|>>|<cell|<math-it|<text|>prim>>>|<row|<cell|>|<cell|<text|\|>>|<cell|\<tau\><rsub|1>\<rightarrow\>\<tau\><rsub|2>>>|<row|<cell|>|<cell|<text|\|>>|<cell|<around*|[|\<tau\>|]>>>|<row|<cell|>|<cell|<text|\|>>|<cell|<around*|(|\<tau\><rsub|1>,\<tau\><rsub|2>|)>>>|<row|<cell|>|<cell|>|<cell|>>|<row|<cell|prim>|<cell|\<colons\>=>|<cell|\<bbb-Z\>>>|<row|<cell|>|<cell|<text|\|>>|<cell|\<bbb-B\>>>>>
  </eqnarray*>

  <doc-data|<doc-title|Unification Rule>>

  <\eqnarray*>
    <tformat|<table|<row|<cell|\<cal-U\><around*|(|\<alpha\>,\<alpha\>|)>>|<cell|=>|<cell|\<bot\>>>|<row|<cell|\<cal-U\><around*|(|\<bbb-Z\>,\<bbb-Z\>|)>>|<cell|=>|<cell|\<bot\>>>|<row|<cell|\<cal-U\><around*|(|\<bbb-B\>,\<bbb-B\>|)>>|<cell|=>|<cell|\<bot\>>>|<row|<cell|\<cal-U\><around*|(|\<alpha\>,\<tau\>|)>\<vee\>\<cal-U\><around*|(|\<tau\>,\<alpha\>|)><text|>>|<cell|=>|<cell|<around*|{|<around*|(|\<alpha\>,\<tau\>|)>|}>
    if \<alpha\> is not free in \<tau\>>>|<row|<cell|\<cal-U\><around*|(|\<tau\><rsub|1>\<rightarrow\>\<tau\><rsub|2>,\<tau\><rsub|1><rsup|<rprime|'>><rsub|<rsup|>><rsup|>\<rightarrow\>\<tau\><rsub|2><rsup|<rprime|'>>|)>>|<cell|=>|<cell|\<cal-U\><around*|(|\<tau\><rsub|1><rsup|>,\<tau\><rsub|1><rsup|<rprime|'>>|)>\<cup\>\<cal-U\><around*|(|\<tau\><rsub|2>,\<tau\><rsub|2><rsup|<rprime|'>>|)>>>|<row|<cell|\<cal-U\><around*|(|<around*|[|\<tau\>|]>,<around*|[|\<tau\><rsup|<rprime|'>>|]>|)>>|<cell|=>|<cell|\<cal-U\><around*|(|\<tau\>,\<tau\><rsup|<rprime|'>>|)>>>|<row|<cell|\<cal-U\><around*|(|<around*|(|\<tau\><rsub|1>\<ast\>\<tau\><rsub|2>|)>,<around*|(|\<tau\><rsub|1><rsup|<rprime|'>>,\<tau\><rsub|2><rsup|<rprime|'>>|)>|)>>|<cell|=>|<cell|\<cal-U\><around*|(|\<tau\><rsub|1>,\<tau\><rsub|1><rsup|<rprime|'>>|)>\<cup\>\<cal-U\><around*|(|\<tau\><rsub|2>,\<tau\><rsub|2><rsup|<rprime|'>>|)>>>|<row|<cell|otherwise>|<cell|=>|<cell|unification
    rejects>>>>
  </eqnarray*>

  <doc-data|<doc-title|Type Inference Rule>>

  <\eqnarray*>
    <tformat|<cwith|2|2|3|3|cell-hyphen|t>|<table|<row|<cell|\<cal-W\><around*|(|\<Gamma\>,x|)>>|<cell|=>|<cell|<hspace|1>
    <around*|(|\<varnothing\>,<math-it|instantiate><around*|(|\<tau\>|)>|)>,where
    \<Gamma\>\<vdash\>x:\<tau\>>>|<row|<cell|\<cal-W\><around*|(|\<Gamma\>,\<lambda\>x\<rightarrow\>e|)>>|<cell|=>|<cell|<math-bf|
    let> \ <around*|(|S<rsub|>,\<tau\><rsub|>|)>=\<cal-W\><around*|(|\<Gamma\><rsub|\<setminus\>x>\<cup\><around*|{|x:\<beta\>|}>,e|)>,fresh
    \<beta\>>>|<row|<cell|>|<cell|>|<cell|<math-bf| in>
    \ \ \ \ <around*|(|S,S\<beta\>\<rightarrow\>\<tau\>|)>>>|<row|<cell|\<cal-W\><around*|(|\<Gamma\>,e<rsub|1>
    e<rsub|2>|)>>|<cell|=>|<cell|<math-bf| let> <text|><hspace|1>
    <around*|(|S<rsub|1>,\<tau\><rsub|1>|)>=\<cal-W\><around*|(|\<mathGamma\>,e<rsub|1>|)><hspace|3>>>|<row|<cell|>|<cell|>|<cell|<text|><space|2em><around*|(|S<rsub|2>,\<tau\><rsub|2>|)>=\<cal-W\><around*|(|S<rsub|1>\<Gamma\>,e<rsub|2>|)><space|2em><space|2em>>>|<row|<cell|>|<cell|>|<cell|<hspace|3>
    \ \ \ \ \ \ \ \ \ \ \ \ \ \ \ \ \ \ \ \ \ \ <space|2em>S<rsub|3>=<math-it|mgu><around*|(|S<rsub|2>\<tau\><rsub|1>,\<tau\><rsub|2>\<rightarrow\>\<beta\>|)>,fresh
    \<beta\>>>|<row|<cell|>|<cell|>|<cell|<math-bf| in>
    \ \ \ \ \ <around*|(|S<rsub|3>\<circ\>S<rsub|2>\<circ\>S<rsub|1>,S<rsub|3>\<beta\>|)>>>|<row|<cell|\<cal-W\><around*|(|\<Gamma\>,<math-bf|let>
    x=e<rsub|1> <math-bf|in> e<rsub|2>|)>>|<cell|=>|<cell|<math-bf| let>
    \ <around*|(|S<rsub|1>,\<tau\><rsub|1>|)>=\<cal-W\><around*|(|\<Gamma\>,e<rsub|1>|)>>>|<row|<cell|>|<cell|>|<cell|<hspace|1><space|2em><around*|(|S<rsub|2>,\<tau\><rsub|2>|)>=\<cal-W\><around*|(|S<rsub|1>\<Gamma\><rsub|\<setminus\>x>\<cup\><around*|{|x:<math-it|generalize><around*|(|S<rsub|1>\<Gamma\>,\<tau\><rsub|1>|)>|}>,e<rsub|2>|)>>>|<row|<cell|>|<cell|>|<cell|<math-bf|
    in> \ \ \ \ \ <around*|(|S<rsub|2>\<circ\>S<rsub|1>,\<tau\><rsub|2>|)>>>|<row|<cell|\<cal-W\><around*|(|\<Gamma\>,<math-bf|let
    rec> x=e<rsub|1> <math-bf|in> e<rsub|2>|)>>|<cell|=>|<cell|<math-bf| let>
    \ \ \ \ \ \ \ \ \ \ \ \ \ \ \ \ \ \ \ \ \ \ \ \ \ \ \ \ \ \<Gamma\><rsup|<rprime|'>>=\<Gamma\><rsub|\<setminus\>x>\<cup\><around*|{|x:\<beta\>|}>,fresh
    \<beta\>>>|<row|<cell|>|<cell|>|<cell|<hspace|1><space|2em><around*|(|S<rsub|1>,\<tau\><rsub|1>|)>=\<cal-W\><around*|(|\<Gamma\><rsup|<rprime|'>>,e1|)>>>|<row|<cell|>|<cell|>|<cell|<hspace|2>
    \ \ \ <space|1em> \ \ \ \ \ \ \ \ \ \ \ \ \ \ \ \ \ \ \ <hspace|1>
    \ \ \ \ \ \ \ S<rsub|2>=<math-it|mgu><around*|(|\<beta\>,\<tau\><rsub|1>|)>>>|<row|<cell|>|<cell|>|<cell|<hspace|1>
    \ \ \ \ \ \ \ \ \ \ \ \ \ \ \ \ \ \ \ \ \ <around*|(|S<rsub|3>,\<tau\><rsub|2>|)>=\<cal-W\><around*|(|S<rsub|2>\<Gamma\><rsup|<rprime|'>>,e<rsub|2>|)>>>|<row|<cell|>|<cell|>|<cell|<math-bf|
    in><around*|(|S<rsub|3>\<circ\>S<rsub|2>\<circ\>S<rsub|1>,\<tau\><rsub|2>|)>>>>>
  </eqnarray*>

  \ <doc-data|<doc-title|Desuger let rec>>

  <\eqnarray*>
    <tformat|<table|<row|<cell|<math-it|fix>>|<cell|:>|<cell|\<forall\>\<alpha\>.
    <around*|(|\<alpha\>\<rightarrow\>\<alpha\>|)>\<rightarrow\>\<alpha\>>>|<row|<cell|>|<cell|>|<cell|>>|<row|<cell|<math-bf|let
    rec> x=e<rsub|1><math-bf|in> e<rsub|2>>|<cell|\<colons\>=>|<cell|<math-bf|let>
    x=<math-it|fix><around*|(|\<lambda\>x.e<rsub|1>|)> <math-bf|in>
    e<rsub|2>>>>>
  </eqnarray*>
</body>