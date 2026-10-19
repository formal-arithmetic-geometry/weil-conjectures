## Worker report

The module defines `internalHomComparison`, the evaluation transpose `v_V`,
`internalHomTransport` for the endpoint map induced by a natural isomorphism,
`InternalHomComparisonLaws` for the four global comparison laws, and
`InternalHomComparisonLawsAt` for those laws at the image pair in the square.
It states `CategoryTheory.coefMonoidalSquareHomTransport` with proof `sorry`.
The separate predicate `SuccessiveCoefficientHomTransport` supplies the returned
three-index clause.

The theorem hypotheses are rendered explicitly: four independently universed
braided monoidal closed categories `CA`, `CB`, `DA`, `DB`; strong braided
monoidal functors `F`, `G`, `UA`, `UB`; a monoidal natural isomorphism
`h : F ⋙ UB ≅ UA ⋙ G`; and arbitrary objects `K M : CA`. The first conjunct
is the square identity using `internalHomTransport h K M`, whose definition is
`MonoidalClosed.pre h.inv` followed by `ihom.map h.hom`. The second conjunct is
the conjugation formula under exactly the two `IsIso` guards. The third conjunct
quantifies `K M` and transports `InternalHomComparisonLawsAt F K M` to
`InternalHomComparisonLawsAt G (UA.obj K) (UA.obj M)`, so the laws are stated
at the required image pairs. The fourth conjunct is
`SuccessiveCoefficientHomTransport F G UA UB h`.

`SuccessiveCoefficientHomTransport` binds a third index with `FBC`, `FAC`,
`GBC`, `GAC`, and `UC`, composite isomorphisms
`fComp : FAC ≅ F ⋙ FBC` and `gComp : GAC ≅ G ⋙ GBC`, and an explicit coherence
equation for `hAB`, `hBC`, `hAC`. For each pair with the required comparison
isomorphisms it states the transported composition equation, whose right side
contains `GBC.map (G.map (internalHomComparison UA ...))` followed by
`GBC.map (internalHomComparison G ...)` and `internalHomComparison GBC ...`;
this is the typed form of `v_{G_AC} = v_{G_BC} ≫ G_{B,C}(v_{G_{A,B}})` after
endpoint transport. It also states the identity case for every `X Y : DA`:
`internalHomComparison (𝟭 DA) X Y = 𝟙 _`.

The four clauses of `InternalHomComparisonLaws` use Mathlib's
`MonoidalClosed.pre`, `curry`, `uncurry`, `comp`, and the lax/oplax tensorators:
both-variable naturality; evaluation transpose; preservation of arbitrary
tensor–Hom transposes; and internal-Hom composition. The pair-indexed predicate
renders the same four clauses with endpoint `K M` fixed.

The statement dependencies are the Mathlib leaves `CategoryTheory.Category`
(`def-nagata-category`) and `CategoryTheory.MonoidalCategory`
(`def-sfb-monoidal-category`). The module uses Mathlib's
`CategoryTheory.MonoidalClosed`, `MonoidalClosed.curry`, `uncurry`, `pre`,
`comp`, `Functor.LaxMonoidal.μ`, `Functor.OplaxMonoidal.δ`, and
`NatTrans.IsMonoidal`; no private replacement is introduced.

Edge cases checked: arbitrary and identity objects/maps, zero objects, identity
functors, arbitrary independent category and functor universes, and the exact
two comparison-isomorphism guards on the conjugation clause. The three-index
coherence permits identity and composite coefficient changes and does not impose
any fullness, essential-surjectivity, or sheaf comparison hypothesis.

Searches made: `msearch.py ... leanfinder` for “monoidal square internal-Hom
evaluation comparison transport” returned only Cartesian exponential comparison
results; `msearch.py ... loogle` for `"ihomComparison"` returned no match;
`msearch.py ... leansearch` for “internal Hom comparison composite monoidal
functor” returned only `CategoryTheory.MonoidalClosedFunctor.comparison_iso`
and generic adjunction results; `rg` in the upstream `WeilConjectures` and
project `lean/Sheaf` trees found no matching declaration. No existing
declaration has the node's statement.

## Second reading by N8

I reread the returned node, its source, and the module after the H3/H8/H11
repair. The square identity and conjugation formula retain their original
endpoint types and explicit `internalHomTransport`. The former global laws
implication is now pair-indexed at the image objects. The new three-index
predicate explicitly binds coefficient index `C`, both composite functor
identifications, the square coherence equation, the transported composition
equation, and the identity-functor equation. The theorem docstring now records
all eleven proof steps and every declaration docstring names the source place.
The file compiles cleanly with `scompile.py`, with no errors or warnings.

## Maintainer review fix (cc second reader, 2026-10-18)

`SuccessiveCoefficientHomTransport` did not assume that the composite
identifications `fComp : FAC ≅ F ⋙ FBC` and `gComp : GAC ≅ G ⋙ GBC` are
monoidal. The node says they are ("specified monoidal composite
identifications"). Without that assumption the fourth conjunct is false. Take
every category to be `ModuleCat ℚ`, every functor `𝟭` with its standard structure
except `FAC = GAC = 𝟭` with tensorator `2 • 𝟙` and unit `(1/2) • 𝟙` (a braided
monoidal structure), every `h` and both comparisons `𝟙`, and `hAC = 𝟙`. Then
`hAC` is monoidal, the coherence holds, all guards and laws hold, and the
conclusion reads `2 • 𝟙 = 𝟙` on `ihom ℚ ℚ`. The fix adds
`[NatTrans.IsMonoidal fComp.hom]` and `[NatTrans.IsMonoidal gComp.hom]`. It also
adds the node's assumed composition equation for `v_F` as the explicit
hypothesis `_hFComp`, and source places on the docstrings of
`internalHomComparison` and `InternalHomComparisonLaws`. The theorem
signature (`lean.statement`) is unchanged. The fixed file compiles with
nt_compile.py with no errors, and `sorryAx` is the only non-standard axiom.
