## Worker report

The module Sheaf.AlgebraicGeometry.HenselianFlatGroupSplitFibreModel states
AlgebraicGeometry.exists_henselian_flat_group_split_fibre_model. Its sole proof is
`sorry`; it defines no new notion. The node statement and all non-lean fields are unchanged.
The source Tag 0A41 was read in literature/stacks-project/more-algebra.tex,
lemma-henselian-local-limit-G-rings, lines 12674ff, together with the node's complete
finite-Hopf-diagram and specified-residue-isomorphism descent proof.

Clause-by-clause correspondence:

- The commutative henselian local ring is `(C : Type u) [CommRing C]
  [HenselianLocalRing C]`. HenselianLocalRing extends IsLocalRing. Its closed residue field
  is exactly `IsLocalRing.ResidueField C = C ⧸ IsLocalRing.maximalIdeal C`; no field
  replacement or independently chosen residue object is used.
- The group scheme over Spec C is `H : Grp (Over (Spec (.of C)))`. Grp and its isomorphisms
  use Mathlib's group diagrams, hence preserve multiplication, identity, and inverse.
- Affineness, flatness and finite presentation are `[IsAffineHom H.X.hom]`,
  `[Flat H.X.hom]`, `[LocallyOfFinitePresentation H.X.hom]`. The affine hypothesis implies
  quasi-compactness and separatedness, hence quasi-separatedness, so the last binder is
  exactly finite presentation in this context. No finite-presentation clause is discarded.
- The finitely generated additive abelian group is `(M : Type u) [AddCommGroup M]
  [AddGroup.FG M]`, including torsion and the zero group.
- The supplied `a` is an isomorphism from the recorded `ringDiagonalizableGroup
  (IsLocalRing.ResidueField C) M` to the group scalar extension of H along
  `Spec.map (CommRingCat.ofHom (IsLocalRing.residue C))`. Scalar extension is the existing
  finite-product-preserving functor `(Over.pullback ...).mapGrp`.
- The conclusion quantifies `A : CommRingCat.{u}` and `HenselianLocalRing A`, and requires
  `IsGRing A`. The existing IsGRing definition includes IsNoetherianRing A, as well as
  regularity of every prime-localization completion map. Thus both Noetherian and G-ring
  conditions are retained without a redundant second Noetherian conjunct.
- The map to C is `u : A →+* C` with `IsLocalHom u`. For local rings this is precisely
  contraction of the maximal ideal, since a local map reflects units and a ring map
  preserves units. It does not require injectivity.
- The model algebra is `B : CommRingCat.{u}` with `Algebra A B`,
  `Algebra.FinitePresentation A B` and `Module.Flat A B`.
- The group structure is the existential `GrpObj` on the actual over-scheme
  `Over.mk (Spec.map (CommRingCat.ofHom (algebraMap A B)))`. Its underlying scheme is
  literally Spec B, not an arbitrary isomorphic model supplied as another hypothesis.
- `b` is a group isomorphism from this group's pullback along Spec u to H.
- `aA` is a group isomorphism from `ringDiagonalizableGroup
  (IsLocalRing.ResidueField A) M` to the model's closed fibre under the residue quotient A.
- The last equality expresses the exact specified-residue compatibility. On the left,
  `a.hom.hom.hom.left` is followed by H_k → H, then `b.inv.hom.hom.left`, then
  (H_A)_C → Spec B. On the right, `Spec.map` of
  `AddMonoidAlgebra.mapRingHom M (IsLocalRing.ResidueField.map u)` is followed by
  `aA.hom.hom.hom.left` and the projection (H_A)_{k_A} → Spec B. These are the two
  maps D_k(M) → Spec B obtained from the desired compatibility square. The group-algebra
  coefficient map sends each basis e_m to the same e_m and is the canonical projection
  for extension along the induced residue-field embedding. The other pullback projection
  is fixed by the over-scheme structures. Pullback uniqueness makes this equation
  equivalent to (a_A)_k followed by b_k being the given a. Using b inverse merely puts
  the equation over Spec B and avoids introducing comparison maps or arbitrary choices.
- No restrictions on other fibres are present. No characteristic, smoothness,
  commutativity of H, or injectivity of u is assumed. All universes and variables are
  explicit; `set_option autoImplicit false` is active.

Dependency interfaces read and used:

- def-weil-pbc-henselian-terminology: WeilConjectures.Mathlib.RingTheory.Henselian;
  HenselianLocalRing (defined in Mathlib.RingTheory.Henselian; the recorded upstream
  module exposes it and IsStrictlyHenselianLocalRing). Only henselianity is used.
- def-weil-residue-field: Mathlib.AlgebraicGeometry.ResidueField,
  AlgebraicGeometry.Scheme.residueField and Scheme.Hom.residueFieldMap were read.
  The node explicitly uses the local-ring quotient C/m, so the underlying existing
  IsLocalRing.ResidueField, IsLocalRing.residue and IsLocalRing.ResidueField.map are used.
- pqf-def-affine-morphism: Mathlib.AlgebraicGeometry.Morphisms.Affine,
  AlgebraicGeometry.IsAffineHom.
- def-weil-flat-morphism: Mathlib.AlgebraicGeometry.Morphisms.Flat, AlgebraicGeometry.Flat.
- def-sbc-locally-finite-presentation: Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation,
  AlgebraicGeometry.LocallyOfFinitePresentation.
- def-weil-pbc-scheme-conventions has a convention-only record; its exact finite-presentation
  meaning is respected as explained above. All schemes are Mathlib Scheme.
- def-sfb-ring-diagonalizable-group: Sheaf.AlgebraicGeometry.RingDiagonalizableGroup,
  AlgebraicGeometry.ringDiagonalizableGroup (and ringDiagonalizableGroupMap inspected).
  Its underlying Hopf algebra is the actual AddMonoidAlgebra with the specified operations.
- def-pc-fibre-product: Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback,
  CategoryTheory.Limits.pullback and pullback.fst (and pullback.snd inspected).
- def-weil-pbc-g-ring: WeilConjectures.RingTheory.GRing, IsGRing.
- def-weil-pbc-finitely-presented-algebra: Mathlib.RingTheory.FinitePresentation,
  Algebra.FinitePresentation.
- def-weil-pbc-flat-ring-map: Mathlib.RingTheory.RingHom.Flat, Module.Flat and RingHom.Flat.

The recorded, stated non-Mathlib proof dependencies are imported without `public`:
WeilConjectures.Mathlib.Algebra.Category.Ring.FinitePresentation
(CommRingCat.exists_isPushout_of_finitePresentation),
Sheaf.RingTheory.ColimitCategoryFpAlgebras
(RingHom.exists_map_of_finitePresentation_colimit), and
WeilConjectures.RingTheory.ColimitFlatRingMap
(RingHom.exists_eventually_flat_of_colimit_flat). Their source signatures and docstrings
were read. Mathlib proof interfaces for affine finite presentation and flatness are already
exposed by the statement imports. The affine spectrum and affine tensor-product pullback
interfaces are exposed by RingDiagonalizableGroup's Mathlib imports. The two proof nodes
lem-sfb-henselian-local-g-ring-colimit and lem-sfb-subgroup-algebra-coset-presentation have
no recorded declaration yet; they are proof-only prerequisites, not notions needed to type
this theorem, and no unrecorded postponed helper is introduced here.

Edge cases checked before writing: M = 0 gives the trivial diagonalizable group, torsion M
(including p-torsion in characteristic p) needs no smoothness and remains allowed; C a field
is allowed; u may have a kernel (no injectivity or monomorphism condition); the zero local
ring is excluded by the mathematical local-ring hypothesis itself, while no extra nonzero
condition is imposed on B. The empty group scheme cannot satisfy the identity-section and
specified-residue-isomorphism hypotheses over nonempty Spec C. The input a is arbitrary,
not only a canonical or identity splitting. There is no claim about non-closed fibres.

Searches for an existing statement:

- msearch.py leansearch: "henselian local flat affine group scheme finite presentation
  Noetherian G-ring model specified residue diagonalizable isomorphism". Eight hits:
  HenselianLocalRing, HenselianRing, their structural facts, Field.henselian, and
  general LocallyOfFinitePresentation interfaces. None is the model theorem.
- msearch.py leanfinder: "Descent of a flat finitely presented affine group scheme over
  a henselian local ring to a henselian Noetherian G-ring preserving a specified
  diagonalizable residue fibre". Eight hits on general flatness and formal smoothness;
  no group model statement.
- msearch.py loogle: `"HenselianLocalRing", "Grp"`. No hits.
- msearch.py grep: `henselian.*(model|group)|split.*[Ff]ibre.*[Mm]odel`. No Mathlib hits.
- rg of the same pattern in lean/WeilConjectures and lean/Sheaf: only unrelated invariants
  and ind-etale pair models. Search for the item id in WeilConjectures: no hits.
- rg for group schemes and diagonalizable constructions in both project roots located
  the recorded RingDiagonalizableGroup module; it is reused without a second definition.

Validation: scompile.py N0 lem-sfb-henselian-flat-group-split-fibre-model compiled both its
sandbox and named-library forms with no errors or non-sorry warnings (36.8 s and 11.8 s).
No disputed statement, correction, new definition node, or dependency repair was needed.

## Second reading by N0

This is the worker's clause-by-clause re-reading, not a claimed independent-agent review:
the dispatcher brief forbids starting other agents and assigns independent review to the
maintainer. With the node and final module open, I checked every hypothesis and existential
against the correspondence above. In particular, affineness supplies qcqs; IsGRing contains
Noetherianity; the existential group object is on Spec B itself; both isomorphisms are in
Grp; the compatibility equation uses b inverse in the correct direction and the induced
residue coefficient map, so it retains the supplied a. All six proof steps appear in the
main declaration docstring. No mismatch was found and no statement was changed.
