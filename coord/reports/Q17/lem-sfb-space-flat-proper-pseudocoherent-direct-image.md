## Worker report

The module `Sheaf.AlgebraicGeometry.SpaceFlatProperPseudoCoherentDirectImage` states
the general flat proper finitely presented direct-image theorem and its projective
projection specialization. Both proofs are `sorry`. The one helper definition is the
actual Yoneda map of projective space over `Spec A`; it contains no postponed data or
new proof obligation. No mathematical statement or accepted proof step was changed.

Clause-by-clause comparison:

- The size convention is rendered by explicit universes `u w`, `Scheme.{u}`,
  `AlgebraicSpace S`, and the displayed `HasDerivedCategory.{w}` instances.
  There are no auto-bound variables (`autoImplicit false`).
- The scheme S and spaces Y and Z over S are the binders
  `{S : Scheme.{u}} {Y Z : AlgebraicSpace S}`. The morphism is `g : Y ⟶ Z`.
- Flatness is `_hflat : MapIsFlat g`, exactly the existing predicate testing scheme
  flatness on compatible etale charts.
- Properness is `_hproper : MapIsProper g`, whose definition is separatedness,
  finite type and universal closedness after every algebraic-space base change.
- Finite presentation is `_hfp : MapIsLocallyOfFinitePresentation g ∧
  MapIsQuasiCompact g.hom.hom ∧ MapIsQuasiCompact (pullback.diagonal g.hom.hom)`:
  local finite presentation, quasi-compactness, and quasi-separatedness.
- `F : Y.DerivedModules` is an object of the unbounded derived category of module
  sheaves on the equivalent small affine etale ringed model.
- `_hF : Y.IsPseudoCoherent F` is precisely the existing local finite-free,
  bounded-above representative definition, with bounds and ranks varying locally.
- The conclusion `Z.IsPseudoCoherent ((derivedDirectImage g).obj F)` uses the fixed
  K-injective right derived functor of the chart-limit module direct image.
- The contextual D_QCoh notation is the existing `derivedQCohProperty` and
  `DerivedQCoh` in `AlgebraicSpaceDerivedModules`; the theorem does not add a separate
  quasi-coherence assumption on F. The local finite-free hypothesis supplies it.
- The contextual conventions about tensor and derived pullback do not add an
  operation to this conclusion: the theorem mentions only the existing direct image.
- In the specialization, `(A : CommRingCat.{u})` quantifies over every commutative
  ring, `(X : AlgebraicSpace (Spec A))` is arbitrary, and `(n : ℕ)` includes zero.
  `projectiveSpaceStructureMap A n` uses
  `ProjectiveSpace (ULift.{u} (Fin (n + 1))) (Spec A)`; the coordinate index has n+1
  elements, so this is classical projective n-space, in the correct universe.
- `f : X ⟶ schemeSpace (Over.mk (𝟙 (Spec A)))` displays the structural morphism
  to the representable base. That target is terminal among spaces over Spec A:
  on every scheme test its Yoneda value consists of the unique structural map.
  This parameter adds no restriction or arbitrary comparison map.
- `enlargedFibreProduct f (projectiveSpaceStructureMap A n)` is the actual sheaf
  fibre product, and `enlargedFibreProductFst f (projectiveSpaceStructureMap A n)`
  is its canonical projection to X. The input F is arbitrary pseudo-coherent on
  this product; the conclusion says its canonical derived image is pseudo-coherent.
- Neither theorem assumes Noetherianity, a lower cohomological bound, nonemptiness,
  quasi-compactness of the whole target, or extra hypotheses on X in the specialization.

Dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme`, `Scheme.Hom`.
- `Sheaf.AlgebraicGeometry.AlgebraicSpace`: `AlgebraicGeometry.AlgebraicSpace`, its
  chart-tested representability predicates, `structureSheaf`, `Modules`.
- `Sheaf.CategoryTheory.RingedSiteModules`: `CategoryTheory.ringedSiteModules`, the
  transparent specialization of Mathlib `SheafOfModules`.
- `Mathlib.Algebra.Homology.DerivedCategory.Basic`: `HasDerivedCategory`,
  `DerivedCategory` and its localization functor `DerivedCategory.Q`.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceQuasiCoherentModule`:
  `AlgebraicGeometry.AlgebraicSpace.QCoh`, using Mathlib `SheafOfModules.IsQuasicoherent`.
- `Sheaf.AlgebraicGeometry.AlgebraicSpacePseudoCoherentComplex`:
  `AlgebraicGeometry.AlgebraicSpace.IsPseudoCoherent` (the full signature and
  representative/sieve definition were read).
- `WeilConjectures.AlgebraicGeometry.ProjectiveSpace.Twist`:
  `AlgebraicGeometry.ProjectiveSpace.twist` and the imported `ProjectiveSpace`
  construction and structural morphism; the signature explicitly indexes homogeneous
  coordinates, requiring `ULift (Fin (n+1))` here.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceDerivedModules`: `DerivedModules`,
  `smallModuleDirectImage`, `derivedDirectImage`, `derivedQCohProperty`.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceMorphismProperties`: `MapIsFlat`,
  `MapIsLocallyOfFinitePresentation`, `MapIsProper` and its three defining clauses.
- `Sheaf.AlgebraicGeometry.EnlargedEtaleRingedSite`: `schemeSpace`,
  `enlargedFibreProduct`, `enlargedFibreProductFst`. These keep the actual sheaf
  pullback and its canonical projection; no choice of an arbitrary map is used.

The last four definition owners were already landed and were added to stmt_deps:
`def-sfb-space-derived-module-calculus`, `def-sfb-space-morphism-properties`,
`def-sfb-space-sheaf-fibre-product`, `def-trf-scheme-algebraic-space`.
All available recorded proof-dependency modules are imported without `public`, except
those already needed publicly for the signatures. Mathlib leaves for the homology
sequence, K-injective comparison, scheme flatness and qcqs permanence are imported too.
Proof dependencies with no declaration are documented in the proof docstrings;
they are not new assumptions or duplicate statements in this delivery.

Edge cases checked against the signatures and source:
zero objects (rank zero models allowed), empty source/target (no nonempty binders),
zero rings (CommRingCat imposes no nontriviality), n=0 (one homogeneous coordinate),
arbitrarily negative nonzero cohomology (unbounded ambient D and no lower bound),
non-Noetherian rings, non-qc targets (only the map has qc/qs hypotheses).
Read Stacks `spaces-perfect.tex` at the complete lemma and proof for Tag 0CTN,
and `spaces-more-morphisms.tex` at Tag 0CTT and the projective-projection invocation.
The source additionally states arbitrary base-change compatibility; the node asks
only the pseudo-coherence conclusion, so no such additional conclusion is asserted.

Searches for an existing statement:

- `msearch.py ... leansearch "Derived pushforward of pseudo coherent complexes under
  flat proper morphisms of finite presentation"`: eight hits, ordinary pushforward
  functors and their properties; none is this derived preservation theorem.
- `msearch.py ... leanfinder "Flat proper finitely presented morphisms of algebraic
  spaces preserve pseudo coherent complexes under derived pushforward"`: eight hits,
  scheme flatness, universal openness and flat descent; none matches.
- `msearch.py ... loogle '"PseudoCoherent"'`: zero hits.
- `msearch.py ... grep 'PseudoCoherent|pseudocoherent' AlgebraicGeometry`: zero hits.
- `rg -n 'lem-sfb-space-flat-proper-pseudocoherent-direct-image|pseudoCoherent.*[Pp]ush|
  [Pp]ush.*[Pp]seudoCoherent' lean/WeilConjectures lean/Sheaf`: no existing statement.
- Direct source searches found the existing pseudo-coherence and derived-direct-image
  definitions and the existing scheme-space and sheaf-fibre-product constructions;
  all were reused. The inherited live node has no Lean record and is queued at stage 2.

No STATEMENT-DISPUTED fault, dependency repair, new node, or statement correction.
The inherited stage-1 delivery failure is explicitly superseded for this stage-2
assignment by `coord/brief-stage2.md` section 0 (2026-10-22 handoff).

## Second reading by Q17

This is a separate self-check, not a claim of an independent worker review; the
dispatcher forbids starting other agents and the maintainer independently reviews
the delivery. Reopened both node and module and matched every clause as above.
Checked that the general conclusion uses the K-injective canonical functor, not an
arbitrary functor, and that properness and finite presentation use the recorded space
predicates. Checked the projective map is the Yoneda structural map, base-changed by
the actual sheaf fibre product, with n+1 homogeneous coordinates. Checked no lower
bound, Noetherianity, nontrivial-ring or nonempty-space condition has slipped in.
The only compiler issue found was a line exceeding 100 characters; it was wrapped.
Both theorem bodies remain `sorry` and the helper has fully specified data.
