## Worker report

The module `Sheaf.AlgebraicGeometry.AffineGroupoidNormPrimeSeparation` states
`AlgebraicGeometry.affineGroupoid_norm_prime_separation`, with one `sorry` and no new
definitions. It includes the entire source-fibre assertion and the separating-norm
assertion. No statement correction or dependency-interface repair is needed. The only
change apart from `lean` is adding the already landed definition node
`def-a1-scheme-groupoid-laws` to `stmt_deps`, so the actual groupoid predicate is cited.
No new nodes or dependency modules are delivered.

Read sources: Stacks `groupoids.tex`, the section “Finite flat groupoids, affine case”
and Tag 03BL, `lemma-points`, specifically the finite list of maps `B → k`, prime
avoidance, and the two determinant gaps; `divisors.tex`, Tag 0BD2,
`lemma-finite-locally-free-has-norm`, specifically the multiplication matrix and its
determinant. The stronger zero-at-alpha₀ conclusion is justified by the identity arrow,
exactly as the node's fifth proof step explains. No equality on invariant functions is
assumed or concluded.

Hypotheses, clause by clause:

| Node | Lean rendering |
| --- | --- |
| Algebraically closed field k | `(k : Type v) [Field k] [IsAlgClosed k]` |
| Commutative k-algebras A,B | `(A B : CommRingCat.{u}) [Algebra k A] [Algebra k B]` |
| U=Spec A, R=Spec B | `Spec A`, `Spec B` throughout |
| Source, target, identity, inverse | `(s t : Spec B ⟶ Spec A) (e : Spec A ⟶ Spec B) (i : Spec B ⟶ Spec B)` |
| Composition on the specified fibre product | `(c : pullback s t ⟶ Spec B)` |
| Groupoid on H-points, naturally in H | `hG : Scheme.IsGroupoid s t e i c` |
| All operations are k-morphisms | `hs` and `ht` state scalar compatibility of source and target; the groupoid identities imply it for e,i,c |
| s,t finite locally free | `[s.IsFiniteLocallyFree] [t.IsFiniteLocallyFree]` |
| Sigma=s-sharp and tau=t-sharp | `(Spec.preimage s).hom`, `(Spec.preimage t).hom` |
| Any k-algebra point alpha₁ | `(alpha₁ : A →ₐ[k] k)` |

For the k-morphism assertion, affine-spectrum full faithfulness translates `hs` and `ht`
into commutation with the structural maps to Spec k. For e, use `e ≫ s = 𝟙`; for i,
use `i ≫ s = t`; for c, use `c ≫ s = pullback.snd s t ≫ s`. Thus no omitted scalar
compatibility condition is being silently assumed. Conversely a groupoid on k-scheme
points gives this `Scheme.IsGroupoid`: all-scheme points split according to their
structural map to Spec k, and s,t preserve that map. Naturality follows by precomposition
because the operations are scheme morphisms. The registered predicate was read in full,
including both unit laws, inverse laws, and the associativity orientation of `pullback s t`.

Conclusions, clause by clause:

| Node | Lean rendering |
| --- | --- |
| E₁=B tensor_{A,sigma,alpha₁} k | `letI := (Spec.preimage s).hom.toAlgebra; letI := alpha₁.toRingHom.toAlgebra; k ⊗[A] B` |
| Finite-dimensional over k | `FiniteDimensional k (k ⊗[A] B)` |
| Every prime maximal | `∀ P : PrimeSpectrum (k ⊗[A] B), P.asIdeal.IsMaximal ∧ ...` |
| Residue field canonically k | `Function.Bijective` of the structural map `k → E₁ → P.asIdeal.ResidueField` followed by `(Scheme.Spec.residueFieldIso ... P).inv.hom` into the scheme residue field |
| Primes and corresponding k-points identify with B₁ | `∃ φ : PrimeSpectrum E₁ ≃ {beta : B →ₐ[k] k // beta.toRingHom.comp (Spec.preimage s).hom = alpha₁.toRingHom}, ...` |
| The identification is the canonical tensor one | For each P, `∃! psi : E₁ →ₐ[k] k` with `RingHom.ker psi.toRingHom = P.asIdeal` and `∀ b, psi (1 ⊗ₜ[A] b) = (φ P).val b` |
| B₁ finite | `Finite {beta : B →ₐ[k] k // ...}` |
| B₁ nonempty and contains the identity | `∃ beta`, its source equation, and `beta.toRingHom = alpha₁.toRingHom.comp (Spec.preimage e).hom` |
| Any other point alpha₀ with no arrow from alpha₁ | `∀ alpha₀ : A →ₐ[k] k`, followed by the implication excluding every beta with the source equation and target equal to alpha₀ |
| Exists f with alpha₀(f)=0 | `∃ f g : A, alpha₀ f = 0 ∧ ...` |
| Every beta in B₁ has beta(tau(f)) nonzero | The quantified beta clause `beta ((Spec.preimage t).hom f) ≠ 0` |
| g is the norm of this same tau(f) | The local finite-free affine chart clause inside the same existential over f,g |
| Restrictions are multiplication determinants | The chart equality to `Algebra.norm Γ(Spec A,V)` after installing `(s.app V).hom.toAlgebra` |
| alpha₀(g)=0 and alpha₁(g)≠0 | The final conjunct `alpha₀ g = 0 ∧ alpha₁ g ≠ 0` |
| Nonreduced fibres, varying ranks, stabilizers allowed | No reducedness, domain, global freeness, rank, or freeness-of-action hypothesis |
| No invariant-function agreement | No such binder |

The commuted tensor order is the Mathlib base-change convention recorded on
`def-weil-module-base-change`; `TensorProduct.comm` identifies it with the node's order.
The local `letI` expressions install algebra structures only; there are no `let`-bound
mathematical objects. On each norm chart, the map into global sections is
`(Scheme.ΓSpecIso A).inv`, and its restriction is the actual presheaf restriction.
The input section is the restriction of `(Scheme.ΓSpecIso B).inv (tau f)`. Therefore g
is the norm section of precisely the same f, not an arbitrary separating function.
Existentially supplying the chart-characterized g avoids choosing data from an
unproved existence theorem. These charts characterize the norm uniquely by determinant
base-change compatibility and sheaf gluing, without requiring global freeness of B/A.

Dependency declarations read and used:

- `def-pc-scheme`, `def-weil-affine-spectrum`: `Mathlib.AlgebraicGeometry.Scheme`,
  `AlgebraicGeometry.Scheme`, `Spec`, `Spec.map`; the canonical reverse coordinate map is
  `Spec.preimage` from `Mathlib.AlgebraicGeometry.GammaSpecAdjunction`.
- `def-pc-fibre-product`: `CategoryTheory.Limits.pullback`,
  `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`, reexported by
  `Sheaf.AlgebraicGeometry.SchemeGroupoidLaws`.
- `def-a1-scheme-groupoid-laws`: `AlgebraicGeometry.Scheme.IsGroupoid`,
  `Sheaf.AlgebraicGeometry.SchemeGroupoidLaws` (already landed, added to stmt_deps).
- `def-pc-finite-locally-free`: `AlgebraicGeometry.Scheme.Hom.IsFiniteLocallyFree`,
  `WeilConjectures.AlgebraicGeometry.Morphisms.FiberDegree`; its three parents are finite,
  flat, and locally of finite presentation.
- `def-weil-algebraic-closure`: `IsAlgClosed`,
  `Mathlib.FieldTheory.IsAlgClosed.Basic`, through `.AlgebraicClosure`; the node is a
  Mathlib leaf, so its `mathlib_match` supplies the declaration rather than `lean`.
- `def-weil-module-base-change`: `TensorProduct` and its scalar-extension convention,
  `Mathlib.LinearAlgebra.TensorProduct.Tower`; commutative tensor algebra and its left
  k-algebra structure are from `Mathlib.RingTheory.TensorProduct.Basic`.
- `def-weil-residue-field`: `AlgebraicGeometry.Scheme.residueField` and
  `Scheme.Spec.residueFieldIso`, `Mathlib.AlgebraicGeometry.ResidueField`; the latter
  identifies ideal residue fields with the former in the displayed structural map.
- `lem-pd-finite-locally-free-norm-charts`:
  `AlgebraicGeometry.exists_finiteLocallyFree_norm_charts`,
  `WeilConjectures.AlgebraicGeometry.FiniteLocallyFreeNormCharts`. The theorem's output
  chart condition at W=top is copied as the norm characterization, using global-section
  restriction to the preimage chart to avoid any equality transport for s-preimage(top).
- `def-weil-endomorphism-determinant`: `LinearMap.det`,
  `Mathlib.LinearAlgebra.Determinant`, used by `Algebra.norm` on each finite-free chart.
  No global application of the nonfree fallback determinant occurs.

Proof dependencies are imported through their recorded modules: affine tensor pullbacks
from `Mathlib.AlgebraicGeometry.Pullbacks`; finite morphisms from the norm-charts import;
properness and finite-fibre facts from `Mathlib.AlgebraicGeometry.Morphisms.Proper` and
`.QuasiFinite`; `fieldOfFiniteDimensional` and `FiniteDimensional.exists_mul_eq_one` from
`Mathlib.LinearAlgebra.FiniteDimensional.Basic`;
`IsAlgClosed.algebraMap_bijective_of_isIntegral` from `.IsAlgClosed.Basic`;
`Ideal.subset_union_prime` from `Mathlib.RingTheory.Ideal.Operations`; and
`Algebra.norm_notMem_iff` from `WeilConjectures.Mathlib.RingTheory.Localization.NormTrace`.
The declaration's docstring gives all five proof steps and their DAG uses.

Edge cases checked before and after writing:

- A=0 has no k-algebra map alpha₁ to a field, so the premise cannot be populated; it is
  not excluded by an extra hypothesis. If an alpha₁ exists, the groupoid identity gives
  a point of B₁, hence the fibre is not the zero algebra.
- For the identity groupoid, B₁ has its single identity arrow. If alpha₀=alpha₁, that
  identity contradicts the no-arrow premise; there is no erroneous separation of one
  point from itself.
- Dual-number fibres and product fibres are permitted: neither `IsDomain E₁` nor
  reducedness nor a singleton spectrum is assumed. The norm prime criterion applies to
  all primes, not the domain-only `norm_eq_zero_iff`.
- Distinct charts may have different ranks; all free and finite assertions are inside
  the chart clause. Rank-zero charts away from evaluated points have determinant 1;
  identity arrows prevent an empty fibre at alpha₀ or alpha₁.
- Repeated target points and stabilizers merely give repeated maximal ideals; neither
  injectivity of target on B₁ nor a free group action is imposed.
- k has its own universe v; fibre tensors live in max u v. There is no independent
  small universe for a family of test algebras that could make a hypothesis vacuous.
  `autoImplicit false` checks that every variable and universe is explicitly bound.

Searches (2026-10-24), using the prescribed `msearch.py Q92 <item>` wrapper:

- LeanFinder, “An affine groupoid with finite locally free source over an algebraically
  closed field admits a norm separating points with no arrow between them”: 8 hits,
  including `AlgebraicGeometry.IsSeparated.hasAffineProperty`,
  `Scheme.instIsSeparatedOfIsAffine`, and affine inverse-limit separation lemmas; none
  states groupoid norm separation.
- Loogle, `Algebra.norm, Ideal.IsPrime, Module.Free`: 0 hits.
- LeanSearch, “A finite source affine groupoid admits a determinant norm separating
  points in distinct orbits”: 8 hits, including fundamental domains, finite group-action
  orbit quotients, and `Module.Basis.smul_det`; none is the stated theorem.
- Mathlib grep, `Groupoid|groupoid` in `AlgebraicGeometry`: 0 hits.
- Mathlib grep, `norm_eq_zero_iff|norm.*prime|prime.*norm` in `RingTheory/Norm`: 5 hits,
  all in `Mathlib/RingTheory/Norm/Basic.lean`. `norm_eq_zero_iff` assumes a domain algebra,
  which would incorrectly exclude the present nonreduced/product fibres.
- `rg` in `lean/WeilConjectures` and `lean/Sheaf` for groupoids and norm charts located
  `SchemeGroupoidLaws`, `AffineGroupoidInvariantNorm`, `AffineGroupoidOrbitFibres`, and
  `FiniteLocallyFreeNormCharts`. Their signatures and documentation were read. The
  invariant-norm theorem concludes membership in an equalizer, and the orbit-fibres
  theorem concludes existence of arrows between invariant-equivalent points; neither
  states the present fibre description and separating norm.
- Exact `grep -rn` for this item in `lean/WeilConjectures` gave no hits. Exact-name
  `rg` for `affineGroupoid_norm_prime_separation|norm_prime_separation` in Mathlib,
  `lean/WeilConjectures` and `lean/Sheaf` gave no hits. No private copy is introduced.

No STATEMENT-DISPUTED flag or node fault remains. Compilation used only `scompile.py`.
The first attempt exposed a namespace qualification error for the residue-field
comparison; it was corrected to `Scheme.Spec.residueFieldIso`. A later reading made
its prime/point equivalence explicit on the unique fibre k-point and every pure tensor.
Both compiled cleanly; the final validation and delivery use the prescribed dry run.

## Second reading by Q92

This is the author's separate clause-by-clause rereading, not an independent review;
the maintainer supplies the independent review under the dispatcher protocol.
I reopened the node and the final module together. The six leading conjunctions give,
in order, finite dimension, maximal primes and canonical residue fields, canonical
prime-to-arrow correspondence with the unique fibre k-point, finiteness of B₁,
its identity witness, and the conditional separation assertion. In particular the
first five clauses do not depend on alpha₀ or on the no-arrow condition.

I checked the direction of each coordinate map: beta comp s-sharp is alpha₁,
beta comp t-sharp is the candidate target, the identity is alpha₁ comp e-sharp,
and the norm input is t-sharp(f). The no-arrow quantifier ranges over all k-algebra
maps satisfying the source equation. Both values of g follow the single existential
for f,g and its determinant chart condition; no arbitrary norm map is assumed.

The residue-field map lands in the actual scheme residue field using the inverse of
the registered comparison iso. I changed its namespace qualification after the compiler
located it under `AlgebraicGeometry.Scheme.Spec`. I also replaced an initial kernel-only
specification of the prime/arrow equivalence by the explicit unique fibre k-point and
its evaluations on `1 ⊗ b`, so the claimed point identification is visible in the type.
These are implementation revisions with no change to the DAG statement. The only
added statement dependency names the existing groupoid definition actually used.
All binders, including k's separate universe, remain explicit; no edge case or source
hypothesis was dropped. The docstring retains every proof step of the node.
