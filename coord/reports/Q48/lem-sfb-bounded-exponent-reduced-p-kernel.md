## Worker report

Stage 2, group Q48, item `lem-sfb-bounded-exponent-reduced-p-kernel`.
The module `Sheaf.AlgebraicGeometry.BoundedExponentReducedPKernel` states
`AlgebraicGeometry.exists_nontrivial_reduced_neutral_p_kernel_of_bounded_exponent`.
Its only theorem has proof `sorry`. It adds no definition and changes only the
item's `lean` record. The old ending concerned a stage-1 split, not a stage-2
delivery. The accepted Q83 split is preserved, as directed by brief-stage2 §0.
There is no repair note for this item.

Sources read: Milne, *Algebraic Groups* (2017), Corollary 14.55, printed p.297
(the proof's subgroup `(U'')_red^0`), Proposition 1.34, Corollary 1.39 and
Proposition 1.52. Corollary 14.55 applies the exponent-p classification to
the reduced identity component of the kernel of multiplication by p. The
node makes its implicit nontriviality argument explicit using bounded exponent;
all five accepted proof steps are included in the declaration docstring.

Hypotheses, matched individually:

| Node | Lean |
| --- | --- |
| Field k | `(k : Type u) [Field k]` |
| Characteristic p > 0 | `(p : ℕ) [CharP k p] (hp : 0 < p)` |
| Every element is a p-th power | `hperfect : Function.Surjective (fun a : k => a ^ p)` |
| k-group scheme C | `C : Over (Spec (CommRingCat.of k))`, `[GrpObj C]` |
| Affine | `[IsAffine C.left]` |
| Finite type | `[LocallyOfFiniteType C.hom] [QuasiCompact C.hom]` |
| Smooth | `[Smooth C.hom]` |
| Connected | `[ConnectedSpace C.left]` |
| Commutative | `[IsCommMonObj C]` |
| Nontrivial over k | `hC : ¬ IsIso C.hom` |
| Integer exponent e at least one | `(e : ℕ) (he : 1 ≤ e)`; these are exactly the nonnegative integer values allowed by the node |
| Multiplication by p^e is zero | `hexponent : 𝟙 C ^ (p ^ e) = 1` |

The group on morphisms is the pointwise group, not composition of endomorphisms:
`𝟙 C ^ n` is multiplication by n; `1` is the constant identity map. These are
the existing conventions explicitly documented in GroupScheme.Defs.
`¬ IsIso C.hom` is equivalent to C not being isomorphic to Spec k as a
k-scheme: the structure map is the unique morphism to the terminal k-scheme.
The same convention renders nontriviality of K.

Objects and conclusions, matched individually:

| Node | Lean |
| --- | --- |
| Scheme-theoretic H = ker[p], fibre over the unit | `GrpObj.ker (𝟙 C ^ p)`, whose definition is `pullback f η[C]` |
| K = (H_red)^0 | Existential `K`, with `j : K ⟶ H`, `IsClosedImmersion j.left`, and `j.left.ker = Scheme.IdealSheafData.vanishingIdeal ⟨connectedComponent (GrpObj.onePoint H), isClosed_connectedComponent⟩` |
| K has a group-scheme structure | Existential class-typed binder `(_ : GrpObj K)` |
| Closed subgroup of C | `IsClosedSubgroupScheme (j ≫ GrpObj.kerι (𝟙 C ^ p))` |
| Affine and finite type, as stipulated for all groups | `IsAffine K.left ∧ LocallyOfFiniteType K.hom ∧ QuasiCompact K.hom` |
| Reduced structure | `IsReduced K.left` and the exact kernel-ideal clause |
| Nontrivial | `¬ IsIso K.hom` |
| Smooth | `Smooth K.hom` |
| Connected | `ConnectedSpace K.left` |
| Commutative | `IsCommMonObj K` |
| Multiplication by p is zero | `𝟙 K ^ p = 1` |

The kernel-ideal characterization specifies the actual reduced neutral
subscheme, not an arbitrary nontrivial p-torsion subgroup. A closed immersion
is determined, up to unique isomorphism over H, by its kernel ideal. The
vanishing ideal of the identity component is the radical ideal defining the
reduced induced scheme structure there (Mathlib IdealSheaf.Basic:565 and
IdealSheaf.Subscheme:454,472). The reduction H_red has exactly the same
underlying topological space as H. Its identity component is clopen, so
restricting the reduction to it is the reduced induced closed subscheme on
that component. Thus this characterization is precisely `(H_red)^0`.
It neither changes the component to a set of rational points nor replaces
the canonical inclusion by an unconstrained map. The composite is required
to be a homomorphism into C, fixing the group structure on K. Cancellation
of the kernel inclusion also makes j a homomorphism into H.

The existential packaging supplies the inherited group operations on the
specified closed subscheme, rather than assuming those operations as extra
hypotheses. No data is chosen from this postponed existence theorem in a
definition. The extra displayed reducedness, affineness and finite-type
clauses spell out the stipulated scheme structure and group conventions.

Dependency declarations read and used:

- `def-weil-field`: `Field`, Mathlib.Algebra.Field.Defs:180.
- `def-sc-group-scheme`: `CategoryTheory.GrpObj`,
  Mathlib.CategoryTheory.Monoidal.Grp:43; `IsCommMonObj` and `IsMonHom`,
  Mathlib.CategoryTheory.Monoidal.Mon:1222,213. The recorded complete interface
  is documented in WeilConjectures.AlgebraicGeometry.GroupScheme.Defs.
- `def-weil-finite-type-morphism`: `AlgebraicGeometry.LocallyOfFiniteType`,
  Mathlib.AlgebraicGeometry.Morphisms.FiniteType:43, and `QuasiCompact`,
  Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact:43, as the node's record requires.
- `def-sbc-smooth-morphisms`: `AlgebraicGeometry.Smooth`,
  Mathlib.AlgebraicGeometry.Morphisms.Smooth:62.
- `def-weil-connected-scheme`: Mathlib.Topology.Connected.Basic:705,
  `ConnectedSpace`; its mathlib_match supplies the declaration without a lean record.
- `def-sc-group-scheme-subgroup`: `IsSubgroupScheme` and
  `IsClosedSubgroupScheme`, WeilConjectures.AlgebraicGeometry.GroupScheme.Defs:81,100.
- `def-pc-fibre-product`: `CategoryTheory.Limits.pullback`,
  Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback:95, as used by
  `CategoryTheory.GrpObj.ker`,
  WeilConjectures.Mathlib.CategoryTheory.Monoidal.Cartesian.Grp:83.
- `def-pc-reduced-scheme`: `AlgebraicGeometry.IsReduced`,
  Mathlib.AlgebraicGeometry.Properties:69. The actual ideal and closed
  subscheme constructors used to specify K are the existing
  `Scheme.IdealSheafData.vanishingIdeal` and `Scheme.Hom.ker`.
- The identity point is the existing `AlgebraicGeometry.GrpObj.onePoint`,
  WeilConjectures.AlgebraicGeometry.GroupScheme.Basic:88. It is the image of
  the unique point of Spec k under the unit, exactly as in the node.

All recorded proof modules are available through the imports. In particular,
the non-public imports include PerfectFieldGroupoidImageClosure,
GroupoidScheme, ClosedImmersionProducts, GeometricReducedFiniteTypePerfectField,
the upstream reduced-source closed-immersion factorization, smooth geometric
reducedness, Mathlib Group.Smooth, and the open-immersion lifting interface.
`lem-sfb-finite-type-group-identity-subgroup` has no Lean record yet; its
proof import is not invented. The already implemented identity-component
construction in GroupScheme.Basic is available. This proof-only missing
statement does not prevent stating this item and requires no dependency repair.

Edge cases checked before writing:

- For e = 1, C itself is killed by p and K is C, up to its canonical
  isomorphism; the least-exponent proof handles [1] = id separately.
- G_a over any perfect positive-characteristic field satisfies the conclusion;
  this includes finite fields and does not require infinitely many k-points.
- Length-two Witt vectors illustrate e > 1 and a kernel with nonreduced
  structure; specifying the radical ideal is essential.
- The trivial group is excluded exactly by hC. An empty scheme cannot be a
  group object over a field, since a unit section must exist.
- Alpha_p is excluded by smoothness. A constant nontrivial Z/p group is
  excluded by connectedness. G_m does not have bounded p-power exponent.
- p = 0 is excluded by hp. p = 1 admits no field with CharP k 1. No separate
  primality or algebraic-closedness hypothesis was added.
- One arbitrary universe u is used for k and schemes, with no independent
  universe of test algebras that could make a condition vacuous.

Searches actually run for an existing statement:

- msearch leanfinder: "A smooth connected commutative affine group scheme of
  bounded p power exponent has nontrivial reduced identity component of its
  multiplication by p kernel". Eight hits: perfect closures, IsReduced and
  perfect-ring nilradicals. None is the group-scheme theorem.
- msearch loogle: `"GrpObj", "ker"`. Eight hits, all additive or multiplicative
  commutator whiskering identities; none states this theorem.
- msearch grep, Mathlib/AlgebraicGeometry:
  `reduced.*(kernel|identity)|bounded.*exponent`: zero hits.
- rg over both project source roots:
  `bounded.*exponent|reduced.*[kK]ernel|[kK]ernel.*reduc`. Hits concern unrelated
  module kernels, torsion coefficients and reduced images; no match.
- grep for this exact node id in WeilConjectures: zero hits. rg for the id
  in dag/lean_names_upstream.json: zero hits.
- Read GroupScheme.Defs and the identity-point and identity-component
  declarations in GroupScheme.Basic. These provide the notions, not this theorem.

Validation: scompile.py compiled the sandbox and named library module cleanly
on the server, with no error or non-sorry warning. `autoImplicit` is disabled;
all variables and the universe are explicitly bound. There is no disputed
statement, statement correction, new node or dependency module.

## Second reading by Q48

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
