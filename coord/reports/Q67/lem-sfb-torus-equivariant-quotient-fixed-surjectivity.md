## Worker report

States `AlgebraicGeometry.torus_equivariant_quotient_fixed_surjectivity` in
`Sheaf.AlgebraicGeometry.GroupScheme.TorusEquivariantQuotientFixedSurjectivity`.
The only postponed proof is this named theorem, whose docstring carries all eight
DAG proof steps. Nothing is proved. The additional module defines the universally
fixed-point sets by their actual predicate, without any choice or postponed data.
The item's natural-language statement, proof and proof dependencies are unchanged.
Its statement dependencies gain the new definition and the two already landed
notion nodes used for the split torus and the fppf quotient presentation.

Clause-by-clause reading:

- Algebraically closed field: `{k : Type u} [Field k] [IsAlgClosed k]`.
- Group schemes and homomorphism: `H J R : Grp (Over (Spec (.of k)))` and
  `q : H ⟶ J`, using the recorded `CategoryTheory.GrpObj`, bundled by `Grp`.
- Smooth, connected, affine, finite type for each of H and J: respectively
  `[Smooth H.X.hom]`, `[ConnectedSpace H.X.left]`, `[IsAffine H.X.left]`, and
  `[LocallyOfFiniteType H.X.hom] [QuasiCompact H.X.hom]`, and the corresponding
  J instances. ConnectedSpace includes nonemptiness.
- Split torus of rank r ≥ 0: `r : ℕ` and
  `Nonempty (R ≅ MultiplicativeType.splitTorus k r)`. This is an isomorphism of
  group schemes. Rank zero is the existing tensor-unit group, with no r > 0 bound.
- Algebraic actions: the existing internal `ModObj R.X H.X` and `ModObj R.X J.X`
  supply actual scheme morphisms and unit/associativity laws. The `hH` and `hJ`
  hypotheses require preservation of multiplication on every scheme's points.
  Since the acting points form a group, the action by t has inverse the action
  by t⁻¹; multiplicativity therefore says exactly that the action is by group
  automorphisms, including preservation of identity and inverse.
- Faithful flatness of q: `[Flat q.hom.hom.left] [Surjective q.hom.hom.left]`.
  Equivariance: the existing `[IsModHom R.X q.hom.hom]`, whose action square
  commutes as a morphism of schemes, rather than only on k-points.
- Fixed subgroup functors: existential group schemes HF, JF with closed inclusions
  iH, iJ, and the two range iff conditions using `universalActionFixedPoints`.
  Expanding that definition quantifies over *every* U, V, f : V ⟶ U and
  t : V ⟶ R.X. This is exactly the further-base-change condition. Closed
  immersions make the points factoring through these inclusions unique, so the
  range conditions give their representing property, not merely images of an
  arbitrary map. Representing objects are quantified, not chosen from a sorry.
- Induced map: `qF : HF ⟶ JF` with `qF ≫ iJ = iH ≫ q`. Since iJ is a closed
  immersion, this determines qF uniquely. No arbitrary replacement map is assumed.
- Faithfully flat and finitely presented: `Flat qF... ∧ Surjective qF... ∧
  LocallyOfFinitePresentation qF... ∧ QuasiCompact qF... ∧ QuasiSeparated qF...`.
  Thus finite presentation is global, rather than just local finite presentation.
- Scheme-theoretic kernel `(ker q)^R`: for every U and x : U ⟶ H.X, the image
  of `GrpObj.ker qF.hom.hom` under its canonical inclusion followed by iH
  consists exactly of x with `x ≫ q.hom.hom = 1` and universal R-fixedness.
  The first condition is the defining pullback condition for the original
  scheme-theoretic kernel. Equality on all test schemes identifies the closed
  subgroups by Yoneda, retaining nilpotents. It avoids imposing or choosing a
  separate action on a reduced kernel.
- Quotient: `IsFppfGroupQuotient (Grp.ofHom (GrpObj.kerι qF.hom.hom)) qF`.
  The existing definition includes the kernel square, local surjectivity in the
  actual fppf topology, representable sheafness, the canonical (g,n) ↦ (g,gn)
  torsor identification, and the universal sheafification arrow from the coset
  presheaf. Together with the kernel clause it is precisely the asserted quotient.
- The final sentence forbids an extra kernel regularity restriction: none occurs.
  In particular there is no smoothness, reducedness, connectedness or étaleness
  hypothesis on either the original kernel or the induced kernel.

Dependencies read and reused:

- `Mathlib.Algebra.Field.Defs`: `Field`.
- `Mathlib.FieldTheory.IsAlgClosed.Basic` (exposed by the recorded torus module):
  `IsAlgClosed`; the algebraic-closure node explicitly records this notion too.
- `Mathlib.CategoryTheory.Monoidal.Grp`: `GrpObj`, `Grp`, `Grp.ofHom`;
  `WeilConjectures.AlgebraicGeometry.GroupScheme.Defs` and its Cartesian group
  interface: `IsMonHom`, `GrpObj.ker`, `GrpObj.kerι`. The kernel is the pullback
  against the identity, as the node requires. The `MonObj` scope exposes the
  existing group structures on hom sets; no local instance is supplied.
- `Mathlib.AlgebraicGeometry.Morphisms.Smooth`: `Smooth`.
- `Mathlib.Topology.Connected.Basic`: `ConnectedSpace`.
- `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`: `LocallyOfFiniteType`, and
  `Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact`: `QuasiCompact`.
- Landed definition node `def-sfb-tori-multiplicative-type`:
  `Sheaf.AlgebraicGeometry.ToriMultiplicativeType`, `MultiplicativeType.splitTorus`.
- Landed definition node `def-sfb-fppf-group-quotient-presentation`:
  `Sheaf.AlgebraicGeometry.GroupScheme.AffineNormalQuotientGeometry`,
  `IsFppfGroupQuotient`. The live source was also read through scompile --source.
- `Mathlib.CategoryTheory.Monoidal.Cartesian.Mod`: `ModObj`, `IsModHom`, and their
  natural actions on point sets. These are existing data, not private action copies.
- The stated proof dependencies are imported privately: HomomorphismFactorization
  (`algebraicGroup_homomorphism_factorization`); the upstream smooth-descent module
  (`Smooth.of_comp_of_flat_of_surjective`); geometrically reduced module
  (`Smooth.geometricallyReduced`); Nullstellensatz module
  (`eq_zero_of_forall_algHom_apply_eq_zero`). Flat composition and finite-presentation
  composition are available through the already necessary Mathlib morphism imports.
  The remaining proof nodes have no recorded declaration and are not assumed in
  the statement or duplicated: they will be proved at their own stage-3 nodes.

Edge cases checked before writing and again against the compiled signature:
rank-zero torus and trivial action recover q itself; identity q has trivial kernel;
trivial target has kernel H; positive-characteristic Frobenius with trivial action
has a possibly infinitesimal kernel and is included. Disconnected finite kernels
such as the Artin–Schreier kernel are included as well. All test schemes, including
empty and nonreduced schemes, are quantified. The group schemes are nonempty by
their units and the connectedness hypotheses. There is no characteristic or
separability restriction. The one explicit universe u is shared with Scheme.{u}
and its category of test schemes, in agreement with the quotient definition; no
independent smaller test-algebra universe makes the fixedness condition vacuous.
The helper itself allows the empty base and any action on any S-scheme.

Searches (all msearch calls used group Q67 and this item):

- LeanFinder: “Torus equivariant faithfully flat homomorphism of smooth connected
  affine algebraic groups is faithfully flat on fixed subgroups”: eight general
  flat-ring results, including `Flat.flat_and_surjective_iff_faithfullyFlat_of_isAffine`,
  none about torus fixed groups.
- Loogle: `"fixed", "surjective"`: three abstract fixed-point/group/field results,
  including `FixedPoints.toAlgAut_surjective`; none is a scheme statement.
- LeanSearch: “A torus equivariant quotient of smooth connected affine group schemes
  induces a faithfully flat finitely presented quotient on fixed groups”: eight
  representation/invariant-quotient results, no matching group-scheme theorem.
- Mathlib grep `fixed.*surject|surject.*centralizer|torus`, AlgebraicGeometry: zero.
- Source and project rg for these names/concepts, plus the exact blueprint item id
  in WeilConjectures: no existing declaration of the item. The relevant existing
  torus-fixed smoothness theorem has only an inline fixedness hypothesis, and the
  abstract-automorphism fixed ideal is a different notion. Both were opened.
- Further LeanSearch, LeanFinder, Mathlib grep and DAG/blueprint searches for the
  universal fixed-point notion are recorded verbatim in the new definition node.
  `blueprint_refs.py ancestor` returned None, inherited in its provenance.

Source check: opened Conrad's PDF online at the node's URL and read the
Corollary 3.3.5 proof on printed p.101, where it invokes surjectivity for torus
centralizers of surjections of smooth connected affine groups. Read the current
blueprint unit and its direct-image proof (3); this item is its inherited supporting
input, not the unit statement. There is no statement dispute or correction.

Validation: the initial compile identified the missing existing `MonObj` scope for
multiplication and identity on point groups; opening that scope repaired it.
Both delivered modules then compiled separately in dependency order through
scompile.py, with clean server confirmation (2.1 s for the definition and 3.5 s
for the theorem). The wrapper's first backend reported no space left on device;
its prescribed server-confirmation backend succeeded, so this did not block work.

## New nodes

`def-sfb-universal-scheme-action-fixed-points` defines
`AlgebraicGeometry.universalActionFixedPoints` in its own module. Its predicate
is the universally quantified fixed-point condition, with actual action and
pullback composition, over an arbitrary scheme S. Source: Conrad Section 2.2
and the item's explicit universal-fixedness convention in Corollary 3.3.5's
centralizer setting. The three Mathlib search kinds and direct source/project
and DAG searches found no reusable definition of this notion; they found only
abstract fixed points and previously stated inline hypotheses. The node has no
postponed data or theorem and adds no regularity or representability assumption.

## Second reading by Q67

The dispatcher brief requires this worker to deliver directly and forbids starting
other agents. Accordingly no independent second worker was used; the maintainer's
independent review is still required. A second self-reading with the node and both
modules open checked the hypothesis/clause correspondence above. It specifically
checked that automorphisms are encoded, that rank zero is allowed, that the induced
map is fixed by its commuting square, that global finite presentation includes
quasi-compactness and quasi-separatedness, and that the kernel is tested on every
scheme rather than just k-points or reduced algebras. No mathematical mismatch was
found; the only elaboration repair was opening Mathlib's existing MonObj scope.
