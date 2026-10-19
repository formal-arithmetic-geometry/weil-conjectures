## Worker report

The module `Sheaf/SixFunctors/EtaleFiniteProjectivePullbackHom.lean` records the
canonical comparison map
`finiteProjectivePullbackHomComparison` and the statement
`AlgebraicGeometry.Etale.finiteProjectivePullbackHom`.  The comparison is the
`Functor.LaxMonoidal.ihomComparison` of the canonical étale inverse-image functor
`upperStar`; it is therefore the map obtained by pulling back evaluation and
currying through the tensor comparison.  The theorem has only a `sorry` proof.

The Lean rendering of the hypotheses and clauses is as follows.

* `A : Type (u + 1)`, `[CommRing A]`, and `[Finite A]` render a finite
  commutative coefficient ring.
* `{S S' : Scheme.{u}}` and `g : S' ⟶ S` render an arbitrary morphism of
  schemes.  The small étale sites and their module categories are the explicit
  `S.smallEtaleTopology`, `S'.smallEtaleTopology`, and
  `ModuleCat.{u + 1} A` occurrences.
* `M : ModuleCat.{u + 1} A` with `[Module.Finite A M]` and
  `[Module.Projective A M]` renders a finite projective A-module, including
  zero modules and finite free modules of rank zero.
* `F : Sheaf S.smallEtaleTopology (ModuleCat.{u + 1} A)` is an arbitrary
  A_S-module sheaf.
* `finiteProjectivePullbackHomComparison A g M F` has source
  `upperStar g (ihom (constantSheaf S M) F)` and target
  `ihom (upperStar g (constantSheaf S M)) (upperStar g F)`, exactly the
  displayed pullback-Hom map.  The first conjunct,
  `IsIso (...)`, is the isomorphism assertion.
* The first universal conjunct quantifies over every finite projective `M'`
  and map `a : M' ⟶ M`; its equation uses
  `MonoidalClosed.pre` and is the contravariant naturality in M.
* The second universal conjunct quantifies over every sheaf `F'` and map
  `b : F ⟶ F'`; its equation uses `ihom.map` and is the covariant naturality
  in F.
* The final equality is `Functor.LaxMonoidal.ihomComparison_ev`: after the
  lax-monoidal tensor map and pulled-back evaluation, the comparison followed
  by evaluation equals evaluation for the pulled-back constant sheaf.  This
  is the required evaluation compatibility.

The declarations used from the statement dependencies are:

* `AlgebraicGeometry.Scheme` and `AlgebraicGeometry.Scheme.Hom` (Mathlib,
  `Mathlib/AlgebraicGeometry/Scheme.lean`) for schemes and morphisms.
* `AlgebraicGeometry.Scheme.Etale` and
  `AlgebraicGeometry.Scheme.smallEtaleTopology` (Mathlib,
  `Mathlib/AlgebraicGeometry/Sites/Etale.lean`) for the small étale sites.
* `CategoryTheory.constantSheaf` (Mathlib,
  `Mathlib/CategoryTheory/Sites/ConstantSheaf.lean`) for constant sheaves.
* `CategoryTheory.ringedSiteModules` (the recorded specialization in
  `Sheaf.CategoryTheory.RingedSiteModules`) for the general sheaf-of-modules
  notion.
* `SheafOfModules.homObj` (the recorded source declaration in
  `WeilConjectures.Algebra.Category.ModuleCat.Sheaf.InternalHom`) for internal
  sheaf Hom.
* `AlgebraicGeometry.etaleInverseImageModulesExact` for the exact étale
  inverse-image module functor and its canonical identification with the
  module pullback.
* `SheafOfModules.module_pullback_tensor_iso` for the canonical tensor
  comparison, and `SheafOfModules.tensorClosed` for the tensor-Hom adjunction.
  The concrete map in this module is supplied by the source's
  `AlgebraicGeometry.Etale.upperStar` and its strong monoidal structure.

I checked the edge cases M = 0, M = A, finite free M = A^r including r = 0,
an idempotent direct summand (for example over Z/6), F = 0, the identity
morphism g, the empty target scheme, and the zero coefficient ring.  None is
excluded by the binders or instances; the comparison remains the canonical
map in each case.

Searches for an existing declaration were made with `msearch.py`: LeanFinder
for “inverse image of internal Hom from finite projective constant module
sheaf” returned only unrelated light-condensed and global-sections results;
Loogle for `Functor.LaxMonoidal.ihomComparison, Module.Projective` returned no
hits (and reported the identifier unknown); grep for `internal hom|ihomComparison`
in Mathlib's module-sheaf directory returned no hits.  I also searched the
project and source trees with `rg` for finite-projective pullback/Hom and
found no competing declaration.  The node's recorded LeanSearch, LeanFinder,
Loogle, and grep searches likewise report no match.  Thus the canonical
comparison and theorem in this module are the single project declaration.

No statement correction, new definition node, dependency module, or
`STATEMENT-DISPUTED` flag is needed.  The file compiles cleanly with the
prescribed `scompile.py` check; the only proof placeholder is the theorem's
expected `sorry`.

## Second reading by NG

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
