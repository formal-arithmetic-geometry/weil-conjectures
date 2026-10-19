## Worker report

The module `Sheaf.CategoryTheory.YonedaZeroSplice` imports the landed
`Sheaf.CategoryTheory.YonedaDerivedExtComparison` interface. It defines
`CategoryTheory.YonedaExtension.RightSplice`, which records the retained prefix,
the new `P` term, the joining equation through `S.f`, and the final equation
through `S.g`. It defines `IsStandardZero`: degree one is `IsSplit`; higher
extensions have isomorphisms at the two endpoint arrows, zero intervening
objects, and zero arrows between middle objects. The theorem
`splice_equivalent_and_zero` is stated with `sorry` and has no proof data.

The abelian-category hypothesis is the existing instance `[Abelian A]`, rendering
`def-sp-abelian`. `S : ShortComplex A` and `hS : S.ShortExact` render the given
short exact sequence. `T : A` and `n : ℕ` render the fixed coefficient object and
positive extension length. The first existential supplies a standard zero
`(n+1)`-extension of `S.X₁` by `T`; the second supplies a standard zero
`(n+2)`-extension of `S.X₃` by `T`. The third clause supplies a right splice for
every input extension. The fourth clause says every pair of right splices sends
an endpoint-fixed generated equivalence `E.Equivalent E'` to
`G.Equivalent G'`. The fifth says a splice of a standard-zero equivalent prefix
is equivalent to a standard-zero target. `RightSplice` renders every canonical
map and endpoint equation, so no arbitrary map is introduced.

The existing declarations used are `YonedaExtension`, `YonedaExtension.Equivalent`,
and `YonedaExtension.IsSplit` from `Sheaf.CategoryTheory.YonedaDerivedExtComparison`
(node `lem-coef-yoneda-derived-ext-comparison`), and Mathlib's `ShortComplex`,
`ShortComplex.ShortExact`, `ComposableArrows`, `IsIso`, and `IsZero`.

Edge cases checked: `n = 0` makes `IsStandardZero` use the split degree-one
sequence; `n = 1` gives the degree-two zero sequence with no intervening zero
objects; larger `n` has exactly the intervening zero objects. The short exact
relations `S.f ≫ S.g = 0`, monicity of `S.f`, and epicity of `S.g` are retained.
No projective or injective objects, nonempty assumptions, or derived Ext data are
introduced.

Searches: `msearch.py ... leanfinder` for Yoneda splicing returned only derived
Ext sequence operations and no concrete endpoint-zigzag statement; `msearch.py
... leansearch` likewise returned only `CategoryTheory.Abelian.Ext` operations;
`msearch.py ... loogle` for `Ext, zero_comp` returned no matches. Grep of
Mathlib, `WeilConjectures`, and `lean/Sheaf` found the landed
`YonedaExtension` interface but no right-splice/zero-splice statement. The
recorded Mathlib `Ext.zero_comp`/`Ext.comp_zero` declarations concern derived Ext
and do not define this exact sequence construction.

## Second reading by Q117

This is the delivering worker's self-check; the maintainer supplies the independent
review. I reread the node, the file, and the dependency definitions. The saved
packet had an off-by-one error in the higher-degree `IsStandardZero` branch.
For degree `n + 2`, its sequence has vertices `0` through `n + 3`: the first
middle object is vertex `1`, the last middle object is vertex `n + 2`, and the
last endpoint is vertex `n + 3`. I corrected the final isomorphism to the arrow
`(n + 2) → (n + 3)`, the zero-object bounds to `2 ≤ j < n + 2`, and the
zero-middle-arrow bounds to `1 ≤ j < n + 2`. Thus degree two has endpoint
isomorphisms `0 → 1` and `2 → 3`, no intervening zero objects, and the zero
arrow `1 → 2`; degree three has the single zero object at `2` and zero arrows
`1 → 2` and `2 → 3`. Degree one remains the recorded `IsSplit` predicate.

The category and morphism universes are independent and explicit; `[Abelian A]`
is the only category hypothesis. `hS : S.ShortExact` retains exactly the given
short exact sequence, and `n : ℕ` parametrizes every positive degree `m = n + 1`.
The zero-model existentials introduce the node's specified representatives.
`RightSplice` retains all prefix objects and differentials by `prefixIso`, fixes
`T` by `left_comm`, identifies the appended object `P` by `lastIso`, and uses
precisely the joining arrow `d ≫ S.f` and quotient `S.g` in its two final
equations. Splice existence, preservation of the generated endpoint-fixed
equivalence, and annihilation of every equivalent-zero prefix are all explicit
conjuncts of `splice_equivalent_and_zero`. Higher zero models are specified up
to endpoint-fixed isomorphism, and a split degree-one extension is isomorphic
to the indicated biproduct sequence. No projective, injective, or derived-Ext
hypothesis is used. The natural-language node statement requires no correction.

## Validation

The repaired module compiled individually through `scompile.py Q117
lem-coef-yoneda-zero-splice` in both sandbox and library-module forms, with no
errors or warnings. The recorded theorem signature was checked verbatim against
the module, all Lean lines are at most 100 characters, and every universe and
variable is explicitly bound. The sole postponed proof is the named theorem
`CategoryTheory.YonedaExtension.splice_equivalent_and_zero`; both helper
definitions contain real data.

The first dry run reported H2: the saved `lean.statement` incorrectly included
the proof introducer `:= by`. The record now ends immediately before `:=`, as
preflight requires, while retaining the signature verbatim. No Lean signature
or natural-language statement changed for this metadata repair.
