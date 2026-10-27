## Worker report

The module `Sheaf.AlgebraicGeometry.AffineRelationLocalBasisReduction` states
`AlgebraicGeometry.affineGroupoid_local_basis_reduction`, with its entire proof `sorry`.
Two fully constructed auxiliary definitions owned by this same node give its canonical
tensor comparison and expand the conjunction of local conclusions. There are no new
DAG nodes, no dependency repairs, and no changes to the item's statement or dependencies.
All three declarations are listed in `lean.declarations` with source/blueprint docstrings.

Hypothesis and clause correspondence:

- Affine U = Spec A and R = Spec B: `A B : CommRingCat.{u}` and the explicit `Spec` terms.
  A ≠ 0: `[Nontrivial A]`. No nonemptiness or positive-rank assumption is added on B.
- The five specified maps and absolute groupoid: binders `s t e i c` and
  `_hG : IsGroupoidScheme s t e i c`, from the recorded dependency module.
- Finite locally free projections: `[s.IsFiniteLocallyFree] [t.IsFiniteLocallyFree]`.
- Sigma and tau: `(Spec.preimage s).hom`, `(Spec.preimage t).hom`.
  C: their actual `RingHom.eqLocus` subring of A, with its usual inclusion algebra on A.
- The canonical phi: `affineGroupoidInvariantTensorComparison s t` is constructed with
  `Algebra.TensorProduct.productMap`, using sigma's C-algebra structure on B and the
  equality defining C to make tau a C-algebra homomorphism. Its value on a pure tensor
  is definitionally sigma(a) tau(a'). `_hφ` asserts surjectivity of this actual map.
- Every prime: `∀ p : PrimeSpectrum C`. The localization is exactly
  `Localization.AtPrime p.asIdeal`, at the prime complement.
- Existence of D: the first conjunct existentially quantifies a `Type u`, `CommRing`,
  `IsLocalRing` and map f, with `IsLocalHom f`, `f.Flat`, and
  `Infinite (IsLocalRing.ResidueField D)`. Mathlib's `IsLocalRing` extends `Nontrivial`,
  so both D and the localization are nonzero local rings as required. A small witness
  exists by adjoining one indeterminate and localizing as in 03C3.
- Every such choice: the second conjunct quantifies D in arbitrary `Type v`, not just
  the existence witness universe, and assumes exactly locality, flatness and infinite
  residue field. It concludes `f.FaithfullyFlat` for each choice, together with
  `IsAffineGroupoidLocalBasisData s t p D f`.
- In that definition C acts on D through f composed with the localization map.
  E and F are the actual `A ⊗[C] D` and `B ⊗[C] D`. The explicit
  `Algebra.TensorProduct.rightAlgebra` structures specify the canonical right-factor
  D-actions, rather than the default left-factor algebra structures.
- Sigma_D and tau_D: the existential D-algebra homomorphisms `σD τD` satisfy their
  stated pure-tensor identities for every a and d. These identities determine the
  maps uniquely on the tensor products and hence encode the induced maps, not
  arbitrary replacements.
- Invariant ring exactly D: `Function.Injective (algebraMap D E)` together with
  `∀ x, σD x = τD x ↔ ∃ d, algebraMap D E d = x`. Thus this is an identification
  by the canonical map, not an abstract ring isomorphism or just an equality of images.
- Semilocality: `Finite (MaximalSpectrum E)`. Radical containment:
  `Ideal.map (algebraMap D E) (IsLocalRing.maximalIdeal D) ≤ Ideal.jacobson ⊥`.
  The latter Jacobson radical is the intersection of the maximal ideals of E.
- Single orbit of maximal points: for every pair x,y in `MaximalSpectrum E`, a prime
  z of F has source x and target y via `PrimeSpectrum.comap σD.toRingHom` and tauD.
  Maximal points are included through `MaximalSpectrum.toPrimeSpectrum`.
- Induced groupoid: existential `eD iD cD` satisfy `IsGroupoidScheme` for the fixed
  induced source and target. Both projections are asserted finite locally free.
  This does specify the induced groupoid: the final comparison identifies the arrow
  scheme with the kernel pair of E → D, with those same two projections. A groupoid
  structure on an equivalence relation is unique (identity is the diagonal, inverse
  swaps the coordinates, composition is (x,y),(y,z) ↦ (x,z)). Consequently there is
  no extra choice of groupoid operations and these are the base-changed operations.
- Constant degree: one `r : ℕ` with `1 ≤ r` and the source's
  `IsFiniteLocallyFreeOfDegree r`. The recorded definition's `fiberDegree_eq`
  quantifies over every point; `fiberDegree` is exactly the residue-field dimension
  of global sections of the scheme-theoretic fibre, not the number of fibre points.
- The elements: one `x : Fin r → E` is shared by both basis clauses.
  `∀ b : F, ∃! a : Fin r → E, b = ∑ j, σD (a j) * τD (x j)` says precisely that
  tauD(x_j) form an E-basis via sigmaD. The second clause supplies a
  `Module.Basis (Fin r) D E` whose vectors equal this same x_j.
- Finite freeness: explicitly `Module.Finite D E ∧ Module.Free D E`.
- Final canonical isomorphism: a ring equivalence `φD : (E ⊗[D] E) ≃+* F` with
  `∀ a b, φD (a ⊗ₜ b) = σD a * τD b`. The formula uniquely determines the
  comparison, so no arbitrary isomorphism replaces it.

Statement dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Spec`, `Spec.map`;
  `Mathlib.AlgebraicGeometry.GammaSpecAdjunction`: `Spec.preimage` (also read `Spec.homEquiv`).
- `Sheaf.AlgebraicGeometry.GroupoidScheme`: `AlgebraicGeometry.IsGroupoidScheme`.
- `WeilConjectures.AlgebraicGeometry.Morphisms.FiberDegree`:
  `Scheme.Hom.IsFiniteLocallyFree`, `IsFiniteLocallyFreeOfDegree`, and `fiberDegree`.
- `Mathlib.LinearAlgebra.TensorProduct.Defs`: `TensorProduct`, through
  `Mathlib.RingTheory.TensorProduct.Maps` and its algebra tensor universal property.
- `Mathlib.RingTheory.RingHom.Flat`: `RingHom.Flat` (the recorded flat-map definition).
- `Mathlib.RingTheory.Flat.FaithfullyFlat.Basic`: `Module.FaithfullyFlat`, through
  `Mathlib.RingTheory.RingHom.FaithfullyFlat`: `RingHom.FaithfullyFlat` (explicitly
  named in the dependency's recorded declarations and mathlib_match).

All available recorded proof-dependency modules are plain imports: FlatLocalExtensionGivenResidueField,
Flat.FaithfullyFlat.Algebra, Flat.Localization, Flat.Basic, AffineGroupoidIntegralInvariants,
AffineGroupoidOrbitFibres, Ideal.GoingUp, Morphisms.QuasiFinite/Proper/UniversallyClosed,
AffineGroupoidInvariantRankStrata, Modules.FinitePushforward, Modules.LocallyFreeAffine,
FiniteProjectiveStandardFreeCover, TensorProduct.RightExactness, SemilocalSubmoduleBasis,
and AffineGroupoidBasisDescent. The node
`lem-a1-affine-groupoid-basechange-polynomial-norm` currently has no recorded Lean module;
its proof use remains in the theorem's eight-step docstring and no fictitious import
is introduced. It is not needed to type the statement. The integral-invariants proof
interface uses the separately landed `Scheme.IsGroupoid`; this delivery uses the item's
recorded `IsGroupoidScheme`, without redeclaring either groupoid notion. A bridge is a
proof-stage concern, not an extra assumption in this statement.

Sources read: the entire 03BM proposition and proof; 03C8 and its proof; algebra.tex
03C1 and 03C3. The current blueprint ancestor `lem-a1-affine-hc0` has the H_c^0 vanishing
statement, as the node's provenance record says; the concrete statement here follows
the named Stacks proof paragraphs, not an invented paragraph of that ancestor.

Edge cases checked: the zero A case is explicitly excluded by the node; local rings
are nonzero by their class, and injectivity of D → E excludes empty Spec E. The
identity groupoid has rank one; a transitive two-point pair groupoid has rank two.
A nontrivial isotropy group does not satisfy the surjective tensor comparison and
is not silently added. Nonreduced rings and non-Noetherian rings remain allowed;
no reducedness, separability or domain condition appears. The basis index is Fin r
with r ≥ 1, matching the node rather than excluding or adding rank-zero cases.
D may be in any universe v and E,F in max u v. There are no file-local notations,
private definitions, instances or auto-bound variables. The lets are in the body
of the explicit predicate definition, not in the theorem statement.

Searches for an exact existing statement:

- msearch.py leanfinder: “An affine finite locally free groupoid with surjective invariant
  tensor comparison becomes semilocal and finite free after flat local extension with
  infinite residue field”: eight smooth/etale/flat descent hits, no match.
- msearch.py loogle: `Algebra.TensorProduct, Module.Basis, IsSemilocalRing`:
  zero hits, unknown identifier Algebra.TensorProduct (a namespace rather than a declaration).
- msearch.py grep: `affineGroupoid.*(basis|local)|infinite.*residue|IsSemilocalRing`
  in Mathlib AlgebraicGeometry: zero hits.
- rg in WeilConjectures and Sheaf for this item ID and `affineGroupoid.*(local|basis)`:
  only `affineGroupoid_basis_descent`, the recorded proof input, not this statement.
- rg in the upstream declaration index, Mathlib, WeilConjectures and Sheaf for the
  three proposed declaration names: no collisions. RingHom.eqLocus, TensorProduct,
  the right-factor algebra, bases, and the recorded groupoid notion are reused.

The final file is compiled using the prescribed scompile.py, including module mode.
No statement fault or disputed mathematical claim was found.

## Second reading by Q97

This is the author's separate clause-by-clause self-check; no independent worker was
started, as the dispatcher brief explicitly forbids starting agents. The maintainer's
independent review remains the independent reading. I reopened the node and file and
checked each correspondence above. The first compile found the mistaken projection
`x.asIdeal.toPrimeSpectrum`; it was corrected to `x.toPrimeSpectrum`. I also widened
the universal D binder to independent universe v and removed equations comparing
schemes of different universes, using instead the uniqueness of a groupoid structure
on the kernel pair given by the final canonical comparison. The pure-tensor formulas
and the final isomorphism ensure this does not weaken the induced-groupoid clause.
The basis vectors, rank, source scalar action, and invariant D map are shared across
all clauses. The node itself, its proof plan and all statement dependencies are unchanged.
