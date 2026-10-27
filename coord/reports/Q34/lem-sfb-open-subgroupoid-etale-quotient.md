## Worker report

The module `Sheaf.AlgebraicGeometry.OpenSubgroupoidEtaleQuotient` states
`AlgebraicGeometry.AlgebraicSpace.open_subgroupoid_etale_quotient`, with one
postponed theorem proof and no new definitions. The natural-language statement
is unchanged. Source checked directly: Stacks `stacks-morphisms.tex`,
`lemma-quasi-splitting-etale` (0DU2), both paragraphs; its final DM consequence
is the étale atlas criterion of 06N3.

Hypotheses and conclusions, clause by clause:

- The base scheme is `{S : Scheme.{u}}`. All three spaces `V R P` are
  `AlgebraicSpace S`. Independent explicit universes for the two quotient total
  categories use `max u vᵢ` and `max (u + 1) wᵢ`; the big site and all its base
  arrows fit, without equating the two quotient universes.
- Source and target are space maps `s t : R ⟶ V`. Unit, inverse, and composition
  are presheaf maps `e i c`; `hR.groupoid` imposes exactly the groupoid laws on
  every test scheme, with `c(a,b)` meaning a after b. These are the same laws
  as `IsGroupoidScheme`, using the already landed algebraic-space version.
- `hs ht : MapIsFlat ...` and `hsfp htfp : MapIsLocallyOfFinitePresentation ...`
  are the source/target flatness and local finite presentation, tested on all
  compatible pairs of étale scheme charts. No separation, finiteness, or
  quasi-compactness assumption is added.
- `q : P.obj.obj ⟶ R.obj.obj` with `hq : IsRepresentableWith
  (fun _ _ f ↦ IsOpenImmersion f.left) q` is the open subspace. It is an
  inclusion up to its canonical isomorphism onto its image, not an arbitrary
  étale or monic map.
- The objects of both groupoids are literally the same `V`. Source and target
  on P are the composites `q ≫ s.hom.hom` and `q ≫ t.hom.hom`. Unit, inverse,
  and composition on P are `eP iP cP`, with their groupoid laws supplied by
  `hP.groupoid`. `he` says the unit lies in P, `hi` says inverse is restriction,
  and `hc` says composition is restriction along the canonical map on
  composable pairs. Thus no arbitrary subgroupoid structure is substituted.
- `X aR hR` and `Y aP hP` are the quotients `[V/R]` and `[V/P]` in the existing
  `SpaceGroupoidQuotientPresentation` interface. This is a presentation of
  the quotient, not an assumption of algebraicity: the presentation asserts
  precisely fppf stack descent, local essential surjectivity from V, and
  identification of all vertical arrows and their composition with R or P.
  Quotients are represented by variables with this characterization, so no
  arbitrary noncanonical object is chosen from an existence theorem.
- The first two conjuncts are `IsAlgebraicModuliStack Y` and
  `IsAlgebraicModuliStack X`, including representable diagonal and a smooth
  surjective scheme atlas.
- `∃ j β` supplies the induced quotient map and its comparison
  `β : ModuliTwoIso (aP.comp j) aR` on objects. The next universally quantified
  square compares the images of `hP.arrows` with `hR.arrows` along q. For an
  arrow p from x to y it is exactly
  `j(ηP(p)) ≫ β(y) = β(x) ≫ ηR(q(p))`. This pins down the inclusion functor on
  arrows too; in particular a map with a wrong action on stabilizers cannot
  satisfy this comparison. Stackification makes this the canonical extension
  up to compatible 2-isomorphism.
- `IsRepresentableByAlgebraicSpaces j` is scheme-test 2-representability.
  `IsSurjectiveModuliMap j` is exactly field-extension-local object lifting,
  with the actual restriction comparison. `ModuliSpaceTest (@Etale) j` tests
  the actual algebraic-space projection on every étale scheme chart of each
  scheme base change, as required by the node.
- `IsDeligneMumfordModuliStack X → IsDeligneMumfordModuliStack Y` is the final
  DM implication, without a DM hypothesis on either quotient beforehand.

Dependency declarations used:

- Mathlib `AlgebraicGeometry.Scheme` / `Scheme.Hom` (Scheme),
  `IsOpenImmersion` (OpenImmersion), `Flat` (Morphisms.Flat),
  `LocallyOfFinitePresentation` (Morphisms.FinitePresentation), `Etale`
  (Morphisms.Etale), and `Scheme.fppfTopology` (Sites.Fpqc).
- `Sheaf.AlgebraicGeometry.AlgebraicSpace`: `AlgebraicSpace`,
  `AlgebraicSpace.IsRepresentableWith` and its scheme-chart conventions.
- `Sheaf.AlgebraicGeometry.StablePointedModuliGroupoids`: `discreteModuli`,
  `discreteModuliMap`, `ModuliTwoIso`, `IsRepresentableByAlgebraicSpaces`, and
  `IsDeligneMumfordModuliStack`; their full signatures and definitions were read.
- `Sheaf.AlgebraicGeometry.GroupoidScheme`: `IsGroupoidScheme` (the recorded
  scheme laws, imported per the node; the applicable space laws are below).
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceGroupoid`:
  `AlgebraicSpace.IsPresheafGroupoid`.
- `Sheaf.AlgebraicGeometry.SpaceGroupoidQuotientPresentation`:
  `SpaceGroupoidQuotientPresentation` and its arrow comparison.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceMorphismProperties`:
  `AlgebraicSpace.MapIsFlat`, `MapIsLocallyOfFinitePresentation`.
- `Sheaf.AlgebraicGeometry.AlgebraicModuliStack`: `IsAlgebraicModuliStack`.
- `Sheaf.AlgebraicGeometry.DmStackMorphismProperties`: `ModuliSpaceTest`.
- `Sheaf.AlgebraicGeometry.StackChartwiseSmoothEtaleCalculus`:
  `IsSurjectiveModuliMap`, owned by definition node
  `def-sfb-surjective-moduli-map`. The stated chartwise calculus is a proof
  dependency only. This module remains a public import because its plain
  surjectivity definition occurs in the signature.
- `Sheaf.CategoryTheory.GroupoidStackificationLocalDescription`:
  `Pseudofunctor.exists_groupoid_stackification_local_description`; imported
  as the recorded statement/proof dependency. The quotient presentation is the
  already landed total-category local-description interface, so no private
  duplicate or new bridge definition is necessary.

The five added statement dependencies are landed existing nodes, not new nodes:
`def-sfb-space-groupoid-quotient-presentation`,
`def-sfb-algebraic-space-groupoid`, `def-sfb-space-morphism-properties`,
`def-sfb-dm-stack-morphism-properties`, and
`def-sfb-surjective-moduli-map`. They supply the declarations
listed above. All other statement dependencies and all proof dependencies are
preserved. Stated proof inputs are imported; remaining unstated proof inputs
are named with their complete route in the theorem docstring.

Edge cases checked before writing: P=R gives the identity quotient map;
P equal to the unit subgroupoid is allowed precisely when it is open, e.g. an
étale constant group yields the usual atlas of its classifying stack. Empty V
forces empty arrows and quotients and leaves all conclusions valid, including
surjectivity. A subgroup of a constant group over a field tests the arrow
comparison (it retains stabilizers and gives BH→BG, rather than an orbit-set
quotient). Flat positive-dimensional groups are allowed; the unit subgroupoid
need not be open and is not spuriously admitted. Non-quasi-compact spaces,
nonseparated spaces, arbitrary characteristic and unrelated quotient universe
levels are not excluded. No disputed statement or source fault was found.

Searches for an existing statement (all via prescribed msearch unless marked rg):

- leanfinder: "open subgroupoid of a flat finitely presented groupoid induces a
  representable surjective etale map of quotient stacks": 8 hits on scheme
  flatness, quotient topology, etale loci and etale over-categories; no match.
- loogle: `"Groupoid", "IsOpenImmersion"`: 0 hits.
- Mathlib grep: `Groupoid|groupoid|stackification`, restricted to
  AlgebraicGeometry: 0 hits.
- leansearch: "open subgroupoid induces etale morphism quotient stacks":
  8 hits on schemes and topological quotient groups; no quotient-stack match.
- rg in both `lean/WeilConjectures` and `lean/Sheaf` for
  `quotientStack|QuotientStack|GroupoidAlgebraic|SpaceGroupoid|groupoidStackification|stackification`
  and the exact item id: no existing item theorem. Found and read
  AlgebraicSpaceGroupoid, SpaceGroupoidQuotientPresentation, SiteStackification,
  AlgebraicQuotientFlatRefinement, and AlgebraicClassifyingStackFlatness; reused
  the first three instead of adding notions. The affine action quotients are
  specialized to group actions, so are not this statement.

Validation: scompile.py accepted both the sandbox and final library module with
exit code 0 and no warnings. Next checks are deliver2.py dry run and delivery.
Only the expected theorem-sorry warning is permitted. An initial compiler error
resolved a namespace collision by spelling the presheaf pullback `Limits.pullback`.

## Repair of returned head 89522ae954e6

H2 repaired: replaced `lem-sfb-stack-chartwise-smooth-etale-calculus` in
`stmt_deps` with the landed definition node `def-sfb-surjective-moduli-map`
(existing declaration `CategoryTheory.IsSurjectiveModuliMap`, Q87, 2026-10-24).
Read the owning node and the declaration's full signature and docstring. It is
a plain definition, and the statement uses no theorem choice or conclusion.
The chartwise-calculus theorem remains in `proof_deps`. Updated the five added
statement dependencies listed above. No Lean source, signature, mathematical
statement, or proof dependency changed. The module retains SHA-256
`c17f165327475b69e61925701d9deb95ce448448a07bd679aa21dc9230f3edbc`.

Compared the retained returned packet with current main: the main item still
has no Lean record and its original twelve statement dependencies; its statement
and proof dependencies agree with the returned packet. Rebuilt the node copy
from current main while preserving the delivered Lean record and the repaired
five added dependencies. The delivery wrapper rebases the repaired packet onto
current main and performs the required compilation and preflight.

## Second reading by Q34

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
