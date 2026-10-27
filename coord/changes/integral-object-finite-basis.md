# Definition performance repair

The local carrier declaration `finitePullback` is changed from `abbrev` to
`noncomputable def`, with the same unfolded term and signature. The proof marks
this carrier irreducible locally so elaboration does not repeatedly unfold the
large homological-complex expression. This preserves the declaration's meaning
and is required for the completed theorem to elaborate within the compiler
budget.
