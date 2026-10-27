## Worker report

The module `Sheaf.RingTheory.NearBlowupOrderGenerators` states
`Hironaka.nearBlowup_order_generators`, with its sole proof `sorry`. The two ancillary
real-data definitions construct the base-coefficient evaluation map at the blowup
point and the resulting canonical residue-field algebra. Neither uses a theorem
with postponed proof, a choice, or an arbitrary comparison map. Every variable and
universe is explicitly bound; `autoImplicit` is false.

Read the whole stage-2 brief, stage document, delivery-errors H, worker role,
project setup and tools README. The former compact-object example module is now
withdrawn; its node points to `WeilConjectures.CategoryTheory.CompactObject`.
There is no released repair note for this item. Read the item and every statement
dependency, including the full recorded declaration signatures and docstrings.
Read Hironaka (1970) online, pp.153--156 and Proposition 21 and the concluding
proof, pp.181,187. The latest blueprint locality proof now uses Varshavsky directly;
this item is the explicitly retained historical algebraic branch in its DAG record.
No blueprint unit or source statement is changed.

Clause and hypothesis correspondence:

- Any field F and a nonzero reduced Noetherian local commutative F-algebra R:
  `{F : Type v} [Field F] {R : Type u} [CommRing R] [Algebra F R]`,
  `[Algebra.EssFiniteType F R]`, `[IsReduced R] [IsNoetherianRing R]
  [IsLocalRing R]`. Mathlib's local-ring class already includes nontriviality;
  the redundant explicit Nontrivial binder was removed after the compiler's
  overlapping-instance warning. The field and algebra universes are independent.
- Prime I contained in m: `(I : Ideal R) [I.IsPrime] (hI : I ≤ maximalIdeal R)`.
  The regular-local centre A=R/I is `[IsRegularLocalRing (R ⧸ I)]`.
- No minimal prime contains I: `hcomponents : ∀ p ∈ minimalPrimes R, ¬ I ≤ p`.
  In the ring spectrum, minimal primes over zero are precisely the primes with
  no strictly smaller prime, as requested, with no irreducible-component shortcut.
- G is the published `Ideal.associatedGraded I`, including its canonical R/I action;
  its flatness is `[Module.Flat (R ⧸ I) (Ideal.associatedGraded I)]`.
- S is `Ideal.normalConeFibre I hI`, definition-owned by the landed
  `def-trf-normal-cone-residue-fibre` and implemented as k tensor_A G.
  Tensor symmetry identifies this with the node's G tensor_A k. This uses
  exactly the canonical quotient A action on k, not an arbitrary coefficient map.
- The blowup Y is `AlgebraicGeometry.AffineBlowup I`, the Proj of the published
  Rees algebra. Its point is `y`. `blowupPointEvaluation` composes ΓSpecIso.inv,
  the blowup structure map on global sections, and residue-field evaluation.
  Its kernel is the base prime below y. Thus `hy : m ≤ ker evaluation` says
  precisely that y lies over the closed point: m is maximal and the evaluation
  kernel is proper because the codomain is a field. The quotient lift in
  `blowupPointResidueAlgebra` supplies exactly k → κ(y).
- k is `IsLocalRing.ResidueField R`. The ring R_y is literally the structure
  sheaf stalk at y; `HilbertSamuel.localFunction Y y` is the length of its quotient
  by the (n+1)st power of its maximal ideal. The right side of `hnear` writes
  `(Module.length R (R ⧸ maximalIdeal R ^ (n+1))).toNat` explicitly.
- δ is `Cardinal.toNat (@Algebra.trdeg k (Y.residueField y) _ _
  (blowupPointResidueAlgebra I y hy))`. Essential finite type and the finite-type
  blowup give a finite residue transcendence degree and finite local quotient
  lengths; hence the natural encodings lose no data. `hnear` is the equality
  of functions after exactly δ inclusive summations, with no extra summation.
  `HilbertSamuel.summation` and `localFunction` are reused from the landed
  `def-trf-hilbert-samuel-invariant`; both added definition owners are in stmt_deps.
- Q is `MvPolynomial (Fin e) k`; α is a k-algebra homomorphism onto S by `hα`.
  `hgraded` says α sends each homogeneous polynomial of degree d into the
  k-span of all `normalConeFibreClass I hI d a`, exactly S_d.
  This is the canonical grade, spelled out with existing definitions rather
  than copied into a second grading construction.
- Bijectivity Q_1 → S_1 is `hlinear`: every element of this degree-one span has
  exactly one homogeneous degree-one polynomial preimage. Together with hgraded
  this is exactly the stated bijection; it asserts neither a basis choice nor
  any higher-degree injectivity.
- q is a prime ideal in Q. `hqhom` says it contains every homogeneous component
  of each of its elements, precisely homogeneity. `hq` identifies its membership
  on homogeneous H: whenever αH equals the fibre class of a ∈ I^d, H belongs to q
  if and only if the Rees monomial aT^d belongs to y.asHomogeneousIdeal.
  This is the canonical fibre-point identification in the node, with no chosen
  fibre isomorphism or arbitrary map. Every element of S_d has such a representative:
  coefficients in k lift to R, and a finite k-linear sum of degree-d classes is
  the class of the corresponding sum of their representatives in I^d. Hence the
  condition covers every homogeneous H. Homogeneity then uniquely determines q
  on arbitrary H by its finite homogeneous decomposition. In particular J ⊆ q
  follows by taking the representative zero; the irrelevant ideal is excluded
  because y is a Rees-Proj point. No extra prime restriction is imposed.
- J is literally `RingHom.ker α.toRingHom`, not a new arbitrary ideal.
  The conclusion equates it to the ideal span of H with `α H = 0` and a positive
  degree d such that H.IsHomogeneous d and its image in `Localization.AtPrime q`
  belongs to `(q.map (algebraMap Q (Localization.AtPrime q))) ^ d`.
  This is precisely H/1 ∈ (q Q_q)^d in the ordinary localization. There is no
  replacement by homogeneous localization, dehomogenization, a symbolic ideal,
  finite prescribed generating family, or radical generation.

Dependency declarations used (all read in the local live-source clone):

- Mathlib.RingTheory.EssentialFiniteness: Algebra.EssFiniteType.
- Mathlib.RingTheory.Noetherian.Defs: IsNoetherianRing.
- Mathlib.RingTheory.RegularLocalRing.Defs: IsRegularLocalRing, the ring clause
  of def-weil-regular-scheme; its scheme-only wrapper IsRegularScheme was read
  but is not needed for the regular quotient ring in this statement.
- WeilConjectures.RingTheory.AssociatedGradedRing: Ideal.associatedGraded,
  associatedGradedAlgebra, associatedGradedPiece and its homogeneous inclusions.
- Mathlib.LinearAlgebra.TensorProduct.Defs and Mathlib.RingTheory.TensorProduct.Basic:
  TensorProduct and its commutative algebra structure, reused through normalConeFibre.
- Mathlib.RingTheory.Flat.Basic: Module.Flat, the module clause of the flat-map node.
- Mathlib.AlgebraicGeometry.Scheme: Spec and Spec.map.
- WeilConjectures.Blowup.Affine.Defs: AffineBlowup and AffineBlowup.toSpec.
- Mathlib.AlgebraicGeometry.ProjectiveSpectrum: Proj, ProjectiveSpectrum.asHomogeneousIdeal.
- Mathlib.RingTheory.Length: Module.length.
- Mathlib.RingTheory.AlgebraicIndependent.Basic: Algebra.trdeg.
- Mathlib.AlgebraicGeometry.ResidueField: Scheme.residueField and Scheme.evaluation;
  Mathlib's ΓSpecIso supplies the canonical affine base coefficients.
- Mathlib.Algebra.MvPolynomial.Basic and Mathlib.RingTheory.MvPolynomial.Homogeneous:
  MvPolynomial, IsHomogeneous and homogeneousComponent.
- WeilConjectures.RingTheory.GradedAlgebra.Standard: GradedAlgebra.IsStandard
  was read; standard grading here is the explicit polynomial grading and the
  canonical degreewise image spans, so no extra IsStandard hypothesis is added.
- Mathlib.RingTheory.Localization.AtPrime.Basic: Localization.AtPrime.
- Sheaf.RingTheory.NormalConeDirectrixMinimalPrimes: normalConeFibre,
  normalConeFibreClass and canonical fibre ring/algebra instances, definition-owned
  by def-trf-normal-cone-residue-fibre, not the theorem in that module.
- Sheaf.AlgebraicGeometry.HilbertSamuelInvariant: HilbertSamuel.summation and
  HilbertSamuel.localFunction, owned by def-trf-hilbert-samuel-invariant.

The stated proof dependencies are imported plainly: polynomial regularity,
regular-local quotient kernel parameters, the Rees algebra, affine chart algebra
and chart cover, and finite-type algebra. Four genuine proof inputs currently have
no Lean record (normal-flat-double-initial-ideal, parameter-blowup-algebra-regular,
permissible-blowup-standard-degrees, permissible-adapted-standard-basis); they are
not used as definitions or silently added as hypotheses, and their imports can be
added by the maintainer when stated. The docstring carries the entire nine-step
natural-language proof plan. The module contains no proof beyond its one sorry.

Edge cases checked before writing:

- I=0 has empty Rees Proj, so no y; also excluded by the non-component hypothesis
  for a nonzero Noetherian ring. No fake nonempty point is constructed.
- I=m gives A=k; all definitions and scalar actions specialize correctly.
- J=0 and a regular normal cone give the zero generated ideal, allowing an empty
  generating family. Zero H is homogeneous in every degree and harmless in a span.
- e=0 is allowed; the other assumptions then leave no projective point, rather
  than adding e>0. Positive-degree condition is imposed on generators, not on e.
- δ=0 leaves the local Hilbert function unsummed. n=0 uses R/m of length one.
- Nonclosed y and inseparable residue extensions are retained; no rationality,
  algebraic closedness, perfectness or characteristic-zero hypothesis appears.
- Ordinary prime localization retains the homogeneous scale direction and is
  deliberately not the degree-zero projective local ring.
- Universes u and v are independent for R and F; every geometric object associated
  to R has the canonical universe u.

Searches actually run:

1. msearch.py leanfinder: "At a near point of a permissible blowup, the ideal of
   the projective normal cone is generated by homogeneous polynomials whose local
   order is their degree". Eight results about ProjectiveSpectrum homogeneous
   prime ideals and chart descriptions; no order-generation theorem.
2. msearch.py loogle: "MvPolynomial.IsHomogeneous, ProjectiveSpectrum,
   Ideal.associatedGraded". No hits, unknown identifier Ideal.associatedGraded;
   this service result is not counted as evidence that the project notion is absent.
3. msearch.py leansearch: "Homogeneous kernel generators with order equal to degree
   at a near point of a blowup". Eight hits, including IsHomogeneous,
   homogeneousComponent_isHomogeneous, homogeneousCore and power-series orders;
   none states this theorem.
4. msearch.py grep: "HilbertSamuel|near.point|initial.ideal.*order", RingTheory.
   Zero Mathlib hits. An earlier unrestricted broad order-generation grep returned
   unrelated countable-generation material and no mathematical match.
5. rg in lean/WeilConjectures and lean/Sheaf for normalFibre/normalFiber,
   associatedGraded tensor, nearBlowup/NearBlowup/near_blowup, near-point and
   HilbertSamuel; searched the item id in WeilConjectures and Sheaf. No existing
   theorem. Adaptive searches found the reusable fibre definitions and the
   Hilbert--Samuel definitions cited above, plus adjacent Hironaka statement modules.
   DAG searches found their existing definition owners, so no new node is needed.

No STATEMENT-DISPUTED flag, statement correction, dependency repair or new node.
The two stmt_deps additions are already landed definition nodes, as expressly
allowed by the stage-2 brief. All original DAG fields other than lean and those
additions are preserved.

## Second reading by Q72

A separate manual pass by this dispatcher worker checked the file against the
node after compilation; no subagent was launched, as the assignment forbids it.
The maintainer's independent review remains the independent second reader.
This pass checked that hlinear is a degree-one bijection rather than mere
surjectivity, hq covers every homogeneous representative and fixes the point
prime, hnear has exponent δ rather than δ+1, and the conclusion uses the ordinary
prime localization and ideal equality. It also checked every original hypothesis,
including reducedness, essential finite type, primeness, regular quotient,
normal flatness and the non-component condition. The only compiler issue was the
redundant Nontrivial instance, removed because IsLocalRing already includes it;
this changes no mathematical hypothesis. The two helpers have full real data.
