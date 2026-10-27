## Worker report

This is a stage-2 statement delivery, not a reopening of the accepted stage-1 split.
The current brief-stage2.md §0 explicitly resolves the inherited stage-1 BLOCKED ending;
coord/queue.tsv lists this item in stage 2, and the live node has no Lean record.
No repair note for this item exists in coord/repair-notes. The accepted natural-language
statement, proof, dependencies and all other node fields are preserved; only lean changes.

The module Sheaf.Algebra.Lie.RationalSerrePresentation states
LieAlgebra.rationalSerrePresentation, with one sorry. It also defines the canonical
quotient-generator map LieAlgebra.rationalSerreGenerator with real data and no sorry.
This is an owning-node canonical map, permitted by brief-stage2 §1, not a second
construction of a Lie algebra. It applies the existing quotient projection to
FreeLieAlgebra.of. There are no new nodes or dependency-record repairs.

Hypothesis-by-hypothesis correspondence:

- A finite-dimensional rational vector space is V : Type u with AddCommGroup V,
  Module ℚ V, and FiniteDimensional ℚ V. The universe u is explicit and unrestricted.
- The root set is R : Set V with hfinite : R.Finite. The family of coroots is
  c : R → Module.Dual ℚ V, indexed by the actual subtype of roots.
- R excludes zero by hne : ∀ a : R, (a : V) ≠ 0.
- Spanning is hspan : Submodule.span ℚ R = ⊤.
- Coroot normalization is htwo : ∀ a : R, c a a = 2.
- Integral pairings are hint : ∀ a b : R, ∃ n : ℤ, c a b = (n : ℚ).
- The prescribed reflection permutes R by hreflect : ∀ a : R,
  Set.BijOn (fun v : V ↦ v - c a v • (a : V)) R R.
- Reducedness is hreduced : ∀ a : R,
  R ∩ (Submodule.span ℚ ({(a : V)} : Set V) : Set V) = {(a : V), -(a : V)}.
  The span of the singleton is exactly the rational line in the node.

Conclusion-by-conclusion correspondence:

- Existence of a base is the first conjunct, ∃ r (b : Module.Basis (Fin r) ℚ V).
  Every b i belongs to R; every coordinate b.repr a i equals an integer; and
  either all coordinates of a are nonnegative or all are nonpositive. Uniqueness
  of basis coordinates makes this precisely the node's expansion condition.
- The second conjunct universally quantifies r, b, its membership proof hb, and
  the same integer/sign condition. Thus the realization holds for ANY such base,
  not just the base furnished by the existential conjunct. Fin r enumerates a
  finite base; this imposes no restriction on bases of finite-dimensional V.
- A : Matrix (Fin r) (Fin r) ℤ is constrained by
  ∀ i j, (A i j : ℚ) = c ⟨b i, hb i⟩ (b j). This is the exact prescribed matrix,
  uniquely determined because integer casting into ℚ is injective. Such A exists
  by hint. This binder neither chooses an arbitrary map nor adds a mathematical
  assumption: the implication expresses the conclusion for that prescribed A.
- The algebra is literally Matrix.ToLieAlgebra ℚ A, the free Lie algebra modulo
  CartanMatrix.Relations.toIdeal ℚ A. Reading SerreConstruction.lean:95--153 shows
  HH, EF, HE, HF, adE and adF generate the ideal by LieSubmodule.lieSpan. EF uses
  the diagonal H and zero off diagonal; HE subtracts A_ij E_j, HF adds A_ij F_j.
  For distinct i,j the simple-root hypotheses imply A_ij ≤ 0; Mathlib's
  (ad E_i)^((-A_ij).toNat) [E_i,E_j] is exactly (ad E_i)^(1-A_ij) E_j.
  Diagonal Serre terms are already zero because [E_i,E_i]=[F_i,F_i]=0.
  Thus this is exactly the presented quotient, with all six relation families.
- Finite dimensionality and semisimplicity are separate conjuncts
  FiniteDimensional ℚ (Matrix.ToLieAlgebra ℚ A) and
  HasTrivialRadical ℚ (Matrix.ToLieAlgebra ℚ A). The latter is the dependency's
  recorded predicate, equivalent to having no nonzero solvable ideal.
- Independence of the H_i is LinearIndependent ℚ applied to the images of
  CartanMatrix.Generators.H under rationalSerreGenerator.
- Their Cartan span is an existential LieSubalgebra h whose toSubmodule equals
  Submodule.span ℚ (Set.range ...H...). IsLieAbelian h states commutativity;
  ∀ k, h ≤ k → IsLieAbelian k → k = h states maximality among abelian subalgebras.
- The prescribed identification is θ : h ≃ₗ[ℚ] Module.Dual ℚ V. For each i,
  an element t : h has underlying vector H_i and satisfies θ t = c ⟨b i, hb i⟩.
  This pins down θ on the spanning generators, hence specifies the canonical
  identification and is not an unconstrained equivalence.
- For each a : V, LieModule.weightSpace L (fun t : h ↦ θ t a) is precisely
  {x : L | ∀ t : h, [t,x] = (θ t)(a) • x}. These are ordinary simultaneous
  eigenspaces. Their supremum as rational submodules is top, expressing a
  spanning set of simultaneous eigenvectors and hence diagonal action. Because
  θ is an isomorphism and V is finite-dimensional, a ↦ (t ↦ θ t a) parametrizes
  every linear weight of h. Distinct weights have independent eigenspaces.
- For each nonzero a : V, that ordinary weight submodule differs from bottom
  if and only if a ∈ R. This is equality of the entire set of nonzero weights,
  not just inclusion of the prescribed roots. For each a : R its finrank is 1;
  finite dimensionality is already asserted, so this really means dimension one.
- The coroot clause supplies t : h and opposite root vectors e,f with θ t=c a,
  e in the a-space, f in the -a-space, [e,f]=t and (θ t)(a)=2. The normalization
  makes t nonzero, hence e,f nonzero. The one-dimensional opposite spaces make
  their bracket line exactly ℚt. Since a(t)=2, t is the unique normalized element
  of that line, which is exactly the coroot. Thus θ identifies every coroot with
  the supplied c_a, including nonsimple roots.
- The final r = 0 → Subsingleton L says the generator-free presentation is the
  zero rational Lie algebra, without excluding the empty root system.

Dependency declarations read and used:

- def-wf-lie-algebra is a Mathlib leaf; its mathlib_match is its interface.
  Mathlib.Algebra.Lie.Basic: LieRing, LieAlgebra, LieModule;
  Mathlib.Algebra.Lie.OfAssociative: LieModule.toEnd, LieAlgebra.ad;
  Mathlib.Algebra.Lie.Subalgebra: LieSubalgebra;
  Mathlib.Algebra.Lie.Ideal: LieIdeal = LieSubmodule R L L;
  Mathlib.Algebra.Lie.Solvable: derivedSeriesOfIdeal, derivedSeries, IsSolvable;
  Mathlib.Algebra.Lie.Quotient: lieQuotientLieAlgebra and
  LieSubmodule.Quotient.mk'. Their full signatures and defining fields were read.
  The relevant modules are publicly imported through SerreConstruction and
  Semisimple.Basic; no private copy of the Lie operations or ideals is introduced.
- def-wf-semisimple-lie-algebra is also a Mathlib leaf. Its recorded declarations
  LieAlgebra.HasTrivialRadical (Semisimple.Defs:64) and
  LieAlgebra.hasTrivialRadical_iff_no_solvable_ideals (Semisimple.Basic:67)
  give exactly the predicate used, over ℚ in finite dimension.
- Proof dependency lem-sfb-root-base-rational-integral-spans is a Mathlib leaf:
  RootPairing.Base.mk', Base.toWeightBasis, Base.toCoweightBasis,
  Base.span_int_root_support, Base.span_int_coroot_support. Their source and
  signatures in Base.lean and BaseExists.lean were read. BaseExists is a plain
  proof-only import (it also imports Base). The other proof dependencies have
  no Lean declarations at this delivery, so there are no modules to import yet.
- Mathlib.Algebra.Lie.Weights.Basic: LieModule.weightSpace and mem_weightSpace
  supply the ordinary eigenvector condition, avoiding generalized root spaces.

Edge cases checked before writing:

- R empty: hspan forces V zero, the existential empty base has r=0, and there
  are no generators, so L, h and the dual are zero. HasTrivialRadical accepts
  the zero algebra. The supremum of its weight submodules is both bottom and top.
- Rank one (R={a,-a}, c_a(a)=2): A=[2], the quotient is sl2 over ℚ, the Cartan
  line is independent, the weights are ±a with dimension one, and [e,f]=t,
  a(t)=2 is the usual coroot normalization.
- Reducible systems are allowed: no irreducibility, connectedness, nonempty
  root set or algebraic closedness is assumed. Opposite bases and reorderings
  are covered by the universal base quantifier. Different lengths of roots
  cause no symmetry assumption on A. No extraneous hypothesis on A is present.
- All same-sign tests allow zero coordinates. The criterion for nonzero weights
  excludes a=0, so the Cartan zero-weight subspace is not incorrectly dimension one.
- Arbitrary object universe u is accepted by compilation; the finite presented
  Lie algebra may be small while the finite-dimensional input V lives in Type u.

Sources and searches:

- Read the actual PDF of Milne, printed pp.503--504, 508, and 611--613, using
  pdftotext. C.21 defines a base by the same-sign integer condition; C.22 gives
  existence. Theorem 23.63 uses the free-generator quotient and identifies its
  split Cartan and root system; p.508 explicitly extends to characteristic zero.
  The PDF's displayed Weyl relations have typos: [X_i,X_i]=H_i must read
  [X_i,Y_i]=H_i, its second [H_i,X_j] must read [H_i,Y_j]=-n(i,j)Y_j,
  and J_j in the negative Serre relation must read Y_j. The node and Mathlib
  already have the correct signs and letters. No statement correction is needed.
- msearch.py leanfinder: "Rational Serre presentation finite dimensional semisimple
  Lie algebra simple roots one dimensional root spaces" returned GeckConstruction
  and abstract root-space results. Geck constructs a different subalgebra and its
  semisimplicity result assumes an algebraically closed field, so it is not this
  exact presentation theorem over ℚ.
- msearch.py loogle: "Matrix.ToLieAlgebra" returned the quotient and its instances;
  this provides the construction, not the realization theorem. Used directly.
- msearch.py grep: "ToLieAlgebra|Serre|serre" in Algebra/Lie returned
  SerreConstruction and Lie-basis definitions; no full theorem match.
- msearch.py leansearch: "A reduced rational root system has a Serre presentation
  with semisimple finite dimensional Lie algebra and one dimensional root spaces"
  returned Matrix.ToLieAlgebra, general Killing-form root-space theorems and
  root-system construction. None states this full result about the Serre quotient.
- rg of lean/WeilConjectures and lean/Sheaf for ToLieAlgebra, rationalSerre,
  serreRational, RationalSimpleRoot and the exact node id returned no match.
  A broader Serre/serre search found unrelated cohomology and Serre-category uses.
  There is no existing project declaration for the result or the generator helper.

Validation: scompile.py compiled the file in both sandbox and final library module
modes cleanly (3.4s and 2.1s), with the theorem proof postponed as requested. The
initial compile requested noncomputable on the real free-Lie generator construction;
this was fixed on the helper definition. No theorem was proved, no local notation,
local instance, private abbreviation, hidden let or automatic implicit was used.

## Second reading by NK

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
