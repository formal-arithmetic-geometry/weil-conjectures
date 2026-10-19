## Worker report

The delivery states `AlgebraicGeometry.Scheme.GaloisCoverAction.torsor_subgroup_quotient_finite_etale`
in `Sheaf.AlgebraicGeometry.TorsorSubgroupQuotientFiniteEtale`, with `sorry` as its entire proof.
No definition, extra theorem, new node, dependency repair, or statement correction is needed.
Only the item's `lean` field is changed. Q49's recorded PASS/merge was the Stage 1 split;
it did not supply a Lean declaration. Thus the previous worker's stale-assignment diagnosis
does not apply to this Stage 2 assignment.

The statement was matched to the node hypothesis by hypothesis and clause by clause:

- The nonempty connected scheme U is `{U : Scheme.{u}} [ConnectedSpace U]`.
  `ConnectedSpace` includes nonemptiness; no separate nonempty assumption is needed.
- The finite group is `{G : Type v} [Group G] [Finite G]`. Its universe is independent
  of the scheme universe, as permitted by the recorded Galois-cover interface.
- The given connected finite etale Galois cover is `(c : Scheme.GaloisCoverAction G U)`
  with `[ConnectedSpace c.Z]`. E is exactly `c.Z` and its structure morphism is `c.π`.
  The structure's `isFinite`, `etale`, `surjective`, `smul`, `smul_π`, `one_smul`,
  `mul_smul`, `simply_transitive`, and `quotient` fields give precisely the recorded
  Galois-cover notion. In particular `quotient` is the categorical scheme quotient,
  and `simply_transitive` is expressed on algebraically closed field-valued lifts.
- The arbitrary subgroup and its restricted action are `(H : Subgroup G)` and
  `c.smul h.val` for `h : H`. There is no normality hypothesis.
- The specified morphism of U-schemes is `(Z : Scheme.{u}) (π : c.Z ⟶ Z) (v : Z ⟶ U)`
  with `_hπv : π ≫ v = c.π`. The theorem concerns this actual π and v, rather than
  an existentially chosen quotient or an unrelated isomorphism.
- Its finiteness is `[IsFinite π]`. Invariance, part of being a categorical quotient
  by H, is `hπ : ∀ h : H, c.smul h.val ≫ π = π`.
- The equality O_Z = (π_* O_E)^H is `_hsheaf`: for every open W, the canonical map
  `π.app W` is injective and a section upstairs is invariant if and only if it is
  the image of a section downstairs. This identifies the structure sheaf with the
  invariant subsheaf via the specified map, not via an arbitrary isomorphism.
  `eqToHom (congrArg (fun f ↦ f ⁻¹ᵁ W) (hπ h))` transports the section along the
  equality of inverse-image opens, making the invariance equation well typed.
  This is the existing invariant-section formulation also used in
  `Sheaf.AlgebraicGeometry.TameLogQuotientModification`; no duplicate notion is defined.
- The categorical property in schemes is `_hquotient`: every H-invariant map
  `f : c.Z ⟶ T` to any `T : Scheme.{u}` factors uniquely as `π ≫ q = f`.
  T is unrestricted, rather than only a finite etale U-scheme.
- Surjectivity of the given quotient is the first conclusion `Surjective π`.
- Finite etaleness of its structure map is `IsFinite v ∧ Etale v`.
- Connectedness, including nonemptiness, is `ConnectedSpace Z`.
- Every geometric fibre has the specified cardinality: for all `Ω : Type u`
  with `[Field Ω] [IsAlgClosed Ω]` and `s : Spec (.of Ω) ⟶ U`, the conclusion is
  `Nat.card (v.GeometricFiber s) = H.index`. Here `GeometricFiber` is precisely
  the recorded set of field-valued lifts. `IsFinite v` ensures this set is finite.

Dependency declarations read and used:

- `def-weil-connected-scheme`: Mathlib `ConnectedSpace`, in
  `Mathlib.Topology.Connected.Basic` (class and nonempty field read).
- `def-sbc-normal-dominant-galois`: `AlgebraicGeometry.Scheme.GaloisCoverAction`,
  in `Sheaf.AlgebraicGeometry.NormalScheme` (entire structure and docstring read).
  The unrelated normality/dominance clauses of that definition node are not assumed.
- `def-weil-finite-integral-morphism`: `AlgebraicGeometry.IsFinite`, in
  `Mathlib.AlgebraicGeometry.Morphisms.Finite` (class and docstring read).
- `def-weil-etale-morphism`: `AlgebraicGeometry.Etale`, in
  `Mathlib.AlgebraicGeometry.Morphisms.Etale` (class and docstring read).
- `def-weil-pbc-geometric-fibre`: `AlgebraicGeometry.Scheme.Hom.GeometricFiber`,
  in `WeilConjectures.AlgebraicGeometry.Morphisms.Finite.GeometricFiber`
  (abbreviation and docstring read).

Statement imports are public. Nonpublic proof imports include the existing
`WeilConjectures.AlgebraicGeometry.FundamentalGroup.Basic`,
`WeilConjectures.AlgebraicGeometry.IsFiniteOfFpqcCover`,
`Sheaf.AlgebraicGeometry.FpqcDescentEtale`, and
`Sheaf.CategoryTheory.Galois.StacksGaloisCategory`. Their imported APIs also expose
the recorded scheme coproduct, pullback, fpqc-site and finite-etale-category notions.
The missing local source of `IsFiniteOfFpqcCover` was read using
`scompile.py --source WeilConjectures.AlgebraicGeometry.IsFiniteOfFpqcCover`.
`lem-per-free-finite-group-affine-quotient` has no recorded Lean declaration yet,
so its eventual proof import cannot be added in this statement delivery; it is
named in the proof docstring and is only a proof dependency, not a statement prerequisite.

The six-step proof docstring follows the node: torsor identity; the free H-action
quotient; categorical identification with the given quotient; split right-coset
calculation after pulling back along E; fpqc descent; and fibre cardinality and
connectedness. Local source text was checked at Stacks `groupoids.tex`,
`lemma-invariants-base-change` (03BK), especially part (3), and
`spaces-properties.tex`, `lemma-quotient-scheme` (07S7), including its torsor proof.

Edge cases checked: H = bottom gives index |G|, H = top gives index 1, and the
trivial group is allowed. A nonnormal subgroup (for example a subgroup of order
two in S3) is permitted; inversion compares right cosets with the left cosets
used by `H.index`. The empty U and empty E are excluded exactly by the node's
connectedness convention. No assumption of invertibility of |G| is introduced,
so characteristic dividing |G| is retained. U need not be Noetherian, separated,
affine, or quasi-compact. There is no added equality between universe levels.

Searches for an existing statement (actual commands and results):

- `msearch.py Q35 lem-per-torsor-subgroup-quotient-finite-etale leanfinder`
  with query "A categorical quotient of a connected finite etale Galois cover by
  a subgroup is connected finite etale and its geometric fibres have cardinality
  the subgroup index": eight abstract Galois-category results, including
  `PreGaloisCategory.fiberIsoQuotientStabilizer` and
  `PreGaloisCategory.exists_lift_of_quotient_openSubgroup`; none states the result
  for this specified finite categorical quotient in schemes.
- `msearch.py ... loogle 'AlgebraicGeometry.Scheme.Hom.GeometricFiber, Subgroup.index'`:
  zero hits; Loogle does not index the project declaration `GeometricFiber`.
- `msearch.py ... grep 'torsor|GaloisCover|subgroup.*quotient' AlgebraicGeometry`:
  zero Mathlib hits.
- `rg` on `lean/Sheaf` and the upstream `WeilConjectures` tree for torsor/subgroup
  quotient patterns found `Sheaf.ConstructibleSheaf.ConnectedTorsorSubgroupQuotient`.
  Its full module was read: `Scheme.GaloisCover.exists_connected_subgroup_quotient`
  constructs some quotient and an H-torsor whose total space is isomorphic to E,
  but does not identify the supplied categorical quotient or supply the required
  action compatibility. It is not the present statement; the node's parent review
  records this same distinction.
- `rg` for `torsor_subgroup_quotient_finite_etale` across Mathlib, upstream and
  `lean/Sheaf`: no existing declaration. `rg` for the blueprint item id in the
  upstream source: no occurrence.

Validation: the prescribed `scompile.py Q35 lem-per-torsor-subgroup-quotient-finite-etale
<module file>` completed both sandbox and library-module compilations, each in 2.2 s,
with no diagnostic. Every universe and variable is explicitly bound. The module's
lines are at most 100 characters. No `STATEMENT-DISPUTED` or node fault was found.

## Second reading by Q35

This section records the same worker's second pass; the maintainer supplies the
independent review as specified in the dispatch brief. I reopened the node and the
entire module and checked each binder and conclusion against the mapping above.
In particular the supplied π is invariant and over U, the sheaf condition uses its
canonical map on every open, and unique factorization targets arbitrary schemes.
The conclusion is about that π and v, has all four requested properties, and uses
the dependency's actual geometric-fibre definition and the index of H. The more
general recorded `GaloisCoverAction` avoids the universe restriction of the older
`Scheme.GaloisCover` API. No mathematical mismatch required a change. The previous
worker's Stage 1/Stage 2 confusion was resolved by reading the current node, whose
Lean record was absent before this delivery.
