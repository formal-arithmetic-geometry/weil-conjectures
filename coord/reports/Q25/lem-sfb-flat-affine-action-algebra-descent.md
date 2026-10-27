## Worker report

The item is stated in `Sheaf.AlgebraicGeometry.FlatAffineActionAlgebraDescent`, declaration
`AlgebraicGeometry.SchemeAction.flat_affine_action_algebra_descent`. Its natural-language
statement is unchanged. A new definition module supplies the category of equivariant
algebras, reusing the published `HopfAction.AlgebraCoaction` without copying it. All data
are explicit; the two named theorems have `sorry` proofs and source/proof docstrings.

Hypothesis and clause correspondence:

- The field is `(k : Type u) [Field k]`. `H : Scheme.{u}` with
  `[H.Over (Spec (.of k))]`, `[GrpObj (H.asOver (Spec (.of k)))]`, `[IsAffine H]`
  is exactly an affine group scheme over k. `actionAlgebraAffineHom` constructs the
  affine structure-map instance from those hypotheses. Finite type is the recorded
  conjunction `[LocallyOfFiniteType (H.asOver (Spec (.of k))).hom]` and
  `[QuasiCompact (H.asOver (Spec (.of k))).hom]`. No smoothness is assumed.
- E is `(E : Type u) [CommRing E] [Algebra k E] [Algebra.FiniteType k E]`.
  The action is `[ModObj (H.asOver (Spec (.of k))) (affineActionScheme k E)]`.
  This is the geometric encoding used by the presentation dependency, equivalent
  by the affine spectrum correspondence to the rational algebra coaction in the node.
  The existential `ρ : HopfAction.AlgebraCoaction k Γ(H, ⊤) E` includes precisely
  the counit and coassociativity identities. `IsActionAlgebraCoaction` fixes its map
  as pullback along `(x,h) ↦ h⁻¹ • x`, on every finite tensor expansion.
- U is the dependency's `affineActionScheme k E`, and Y is
  `affineInvariantSpectrum k E (H.asOver (Spec (.of k)))`. The invariant ring is
  the dependency's `affineInvariants`; no finite generation is imposed on it.
  The dependency's existing equalizer used the left action directly. Inversion
  preserves its equalizer, but not the coaction itself; the new right-action map
  explicitly includes inversion and does not silently use the opposite coaction.
- X is literally `torsorGroupoid (H.asOver (Spec (.of k))) (affineActionScheme k E)`.
  `actionAlgebraFibred` extracts its fibred structure from
  `flat_affine_action_stack_presentation.{u, u, u+1, 0, 0}`. Fixing these auxiliary
  test-stack universes only chooses a proof of the same proposition; it imposes
  no equality of universes. Pi is the existing `quotientAtlas`.
- `ActionQuasiCoherentAlgebras` is directly `ObjectProperty.FullSubcategory`
  of `IsQuasicoherentModuliAlgebra` on X, using the predicate from
  `def-sfb-stack-quasi-coherent-algebra`: general-site local free presentations,
  with arbitrary generators. No alternate smooth-chart predicate
  or chartwise assumption is introduced.
- `F` is an equivalence from that full category to
  `HopfAction.EquivariantAlgebra.{u,u,u,u+1} k Γ(H, ⊤) E ρ`.
  Objects have an actual extending coaction and structure map. Morphisms are all
  equivariant E-algebra maps. Their underlying carriers are in the same u+1
  ambient coefficient universe as the existing stack-algebra category.
- The family `j` of ring equivalences, its E-structure equation and its equation
  on every algebra map identify the forward functor with actual atlas evaluation,
  naturally as E-algebras. This is a concrete componentwise natural isomorphism.
  The finite-sum formula using `actionAlgebraTransport` fixes its coaction as the
  presentation transport, rather than an arbitrary coaction on an isomorphic ring.
  The transport is a real arrow between trivial scheme torsors, obtained from
  `trivialTorsorFunctor` with label h inverse. Its contravariant restriction has
  exactly the endpoints appearing in the displayed equation.
- `IsSurjectiveModuliAlgebra f.hom ↔ Function.Surjective (F.functor.map f).val`
  states both directions of the requested identification of surjections, using
  the dependency's locally surjective sheaf-map predicate, not objectwise lifting.
- `r A` is a ring equivalence from `moduliGlobalSectionsRing A.obj.right` to
  `EquivariantAlgebra.invariants (F.functor.obj A)`, whose subring is literally
  `RingHom.eqLocus ρ_D (d ↦ d tensor 1)`. Its atlas equation specifies restriction.
  The next equation asserts naturality for every algebra-sheaf map, with global
  sections transported pointwise. This avoids choosing a second global-section map.
- The existential φ is an actual based functor to the invariant spectrum and has
  the same two-isomorphism on pi as the presentation dependency. `smap` is fixed
  on every object x as pullback of the regular function on Y along φ(x), using
  `actionInvariantObjectMap` and the Gamma-Spec comparison. Thus smap is exactly
  the map induced by φ, not an arbitrary ring map with the desired composite.
  The final equation says its composite with r and canonical atlas comparison j
  is the invariant inclusion into E. Since r identifies global sections with the
  invariant subring and j identifies the structure algebra with E, this is precisely
  the identity of E^H requested in the node.
- There is no finite-generation hypothesis on objects of `EquivariantAlgebra` or
  on quasi-coherent algebra sheaves. All algebras in the existing ambient universe
  are covered. `actionStructureAlgebra` has real identity structure-map data;
  its named quasi-coherence obligation is the rank-one local presentation.

Dependency declarations read and used:

- `Mathlib.Algebra.Field.Defs`: `Field`.
- `Mathlib.CategoryTheory.Monoidal.Grp`: `CategoryTheory.GrpObj`;
  its internal-action companion `ModObj` is the scheme action used by the presentation.
- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Spec`, `Spec.map`.
- `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`: `LocallyOfFiniteType`;
  `Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact`: `QuasiCompact`.
- `Sheaf.AlgebraicGeometry.FlatAffineActionStackPresentation`:
  `SchemeAction.flat_affine_action_stack_presentation`. This reuses the canonical
  `affineActionScheme`, `affineInvariants`, `affineInvariantSpectrum`,
  `affineInvariantProjection`, `torsorGroupoid`, `quotientAtlas` and trivial torsors.
- `Sheaf.AlgebraicGeometry.AdequateModuliSpace`: `CategoryTheory.IsAdequateModuliSpace`,
  read for the quasi-coherence convention; no adequacy assumption is added.
- `Sheaf.AlgebraicGeometry.StackQuasiCoherentAlgebra`:
  `ModuliAlgebraSheaf`, `IsQuasicoherentModuliAlgebra`, `IsSurjectiveModuliAlgebra`,
  `moduliStructureSheaf`, `moduliGlobalSectionsRing`.
- `Sheaf.RingTheory.HopfActionModuleData`: `HopfAction.AlgebraCoaction`, `Counital`,
  `Coassociative`; reused by the new category, not restated.
- `Sheaf.AlgebraicGeometry.HopfCoactionLinearization`:
  `HopfAction.coordinateHopfAlgebra`, owned by the existing definition node
  `def-sfb-coordinate-hopf-algebra`, is the canonical coordinate Hopf instance
  used in the statement by `AlgebraCoaction` and `EquivariantAlgebra`. This node
  is explicitly listed in `stmt_deps`. The linearization theorem and its morphism,
  unit and tensor clauses are used only in the proof plan.
- `Mathlib.CategoryTheory.ObjectProperty.FullSubcategory`:
  `CategoryTheory.ObjectProperty.FullSubcategory`, applied directly to the
  stack-algebra predicate above. No groupoid algebra-descent theorem is needed
  to define this category.
- Proof imports retain `AffineGroupTorsorStackification`, `SchemeGroupoidLaws`,
  Mathlib `tilde.adjunction`, and the upstream modules `ModulePullbackAffineSections`,
  `QuasiCoherentTensorProductAffineSections`, `Modules.QuasiCoherentCokernelImage`.
  `lem-sfb-groupoid-module-descent-tensor-cokernel` has no lean or mathlib_match
  record in the read snapshot, so it has no proof import yet. It is not needed
  to type this statement: the theorem docstring retains its exact role for stage 3.

Edge cases checked before and after writing:

- E and D may be zero rings. No Nontrivial or nonempty-spectrum assumption occurs.
  Empty Spec E produces the empty quotient and the same algebra-descent formulation.
- D may have infinitely many generators. The `n : ℕ` in the formulas describes
  each individual finite tensor expansion, not finite generation of an algebra;
  n=0 is allowed and gives the zero tensor equation.
- Trivial H gives the ordinary affine quasi-coherent algebra dictionary. For a
  trivial action and arbitrary H the category remains the full coaction category.
- Nonreduced groups (including mu_p and alpha_p in characteristic p) are allowed:
  no smoothness, etaleness, reductivity, or restriction to geometric points occurs.
- Noncommutative H is allowed. The explicit inversion in the right-action point
  was checked against source/target and arrow label; omitting it would change the
  coaction law even though it would leave the invariant ring unchanged.
- No finite generation of E^H is assumed. Y is affine by construction regardless.
- Test algebras in the new definition have the common max universe, and its use
  in the theorem matches the existing u+1-valued stack algebra convention.

Sources read: the full forward/inverse construction of Stacks 06WT in
`literature/stacks-project/stacks-sheaves.tex`; Stacks 03LF in `groupoids.tex`;
all statement-dependency records and their defining signatures/docstrings. The
current blueprint direct-image proof (3) was read in `literature/blueprint/latest/`;
this is a supporting node of its inherited coarse-space/alteration chain, not a
change to the blueprint unit statement.

Searches for existing statements/notions (actual msearch calls):

- LeanFinder: “Quasi coherent algebras on an affine action quotient stack are
  equivariant algebras with invariant sections”: eight general quasi-coherence,
  module, and abstract-group invariant hits; no quotient-stack algebra theorem.
- Loogle: `AlgebraCoaction, ComoduleAlg`: zero hits, unknown AlgebraCoaction.
- Mathlib grep: `quotientStack|quotient_stack|AlgebraCoaction`: zero hits.
- LeanSearch: “Category of commutative comodule algebras over a Hopf algebra with
  equivariant structure map”: eight HopfAlgCat/CommBialgCat/CoalgCat results,
  none the required category. Full returned output is in the new node's searches.
- LeanFinder: “Category of commutative algebras with a Hopf algebra coaction
  extending a base algebra coaction”: eight HopfAlgCat/CommBialgCat/BialgCat hits,
  not algebras with a fixed coaction. Mathlib grep
  `AlgebraCoaction|ComoduleAlg|EquivariantAlgebra` returned zero hits.
- rg in `lean/WeilConjectures` found only the finite-permutation affine torsor
  equalizer family. rg in `lean/Sheaf` found the reusable `AlgebraCoaction` and
  the finite-flat groupoid dictionary, whose full signatures were read.
  The exact item id has no upstream/project declaration.
- DAG title/concept search and `tools/blueprint_refs.py search coaction algebra`
  found no coaction-algebra category; `search equivariant algebra` gave sixteen
  unrelated blueprint nodes. The similarly named
  `def-sbc-affine-torsor-equivariant-algebra` was read and is an H-subalgebra of
  functions on Fin d for an abstract permutation action, not this notion.

Validation: scompile.py compiled each module separately in dependency order,
against the live published project, with no errors and no warnings. The only
postponed proofs are `actionStructureAlgebra_quasiCoherent` and
`flat_affine_action_algebra_descent`, both under this item's source/proof documentation.
No node correction, dependency-interface repair, or STATEMENT-DISPUTED issue is needed.

## New nodes

`def-sfb-equivariant-coaction-algebra` defines `HopfAction.EquivariantAlgebra` in
`Sheaf.RingTheory.EquivariantCoactionAlgebra`, together with all equivariant algebra
maps, their category, the underlying-ring functor, and the invariant equalizer subring.
It depends on `def-weil-field` for `Field` and on
`def-sfb-hopf-action-module-data` for its actual `AlgebraCoaction`.
Source: Stacks 06WT algebra objects, in the affine form of Stacks 03LF.
The searches above found no existing category. This definition is not a new
version of AlgebraCoaction and does not impose finite generation. The module
contains only real data and the structural proofs needed to define its category.

## Returned-delivery repair

The independent review of head `9b797cb5b026` identified one unused theorem
statement dependency: `lem-sfb-affine-groupoid-quasicoherent-algebra-descent`
provided only a plain full-subcategory abbreviation. Following correction (b),
`ActionQuasiCoherentAlgebras` now directly applies
`ObjectProperty.FullSubcategory` to `IsQuasicoherentModuliAlgebra` from
`def-sfb-stack-quasi-coherent-algebra`. The theorem dependency and its public
import are removed, and Mathlib's full-subcategory module is imported directly.
This is definitionally the same category, so the theorem signature and all
hypotheses and clauses remain unchanged. The presentation theorem remains a
statement dependency because `actionAlgebraFibred` uses its proved fibred
structure. No statement correction or new node is needed for this repair.

Repair validation: `scompile.py` compiled both delivered modules separately
in dependency order against the current live build with no errors or warnings.
The main theorem signature was compared verbatim with `lean.statement`; the
only node fields differing from the current base are `stmt_deps` and `lean`.

## Repair of head 09dcc87f1f71

H2: added the already-landed definition node `def-sfb-coordinate-hopf-algebra`
to the item's `stmt_deps`. Its recorded declaration is
`HopfAction.coordinateHopfAlgebra` in
`Sheaf.AlgebraicGeometry.HopfCoactionLinearization`. I read its signature and
docstring: for a field k and an affine k-group scheme H it supplies
`HopfAlgebra k Γ(H, ⊤)` via the canonical `affineCoordinateHopfAlgebra (.of k) H`.
This is the instance used by the statement, independently of the linearization
theorem's conclusion. The existing public import already exposes it.

H12: added `def-weil-field` to the new node
`def-sfb-equivariant-coaction-algebra`'s `stmt_deps` and an explicit citation
after its field hypothesis. This owns the `Field` notion already used in its
Lean declaration. Both corrections concern dependency ownership; no Lean source,
theorem signature, hypothesis or conclusion changed. The sandbox item was
compared with the current base, retaining its current metadata and changing
only `stmt_deps` and `lean`.

H2/H12 repair validation: `scompile.py` compiled both delivered modules
separately in dependency order against the live published build, with no errors
or warnings. The unchanged theorem signature still matches `lean.statement`
verbatim.

## Second reading by Q25

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
