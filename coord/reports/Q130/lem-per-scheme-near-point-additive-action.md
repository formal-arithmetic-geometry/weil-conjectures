## Worker report

The delivered module is `Sheaf.AlgebraicGeometry.SchemeNearPointAdditiveAction`.
Its only new declaration is the theorem
`AlgebraicGeometry.HilbertSamuel.scheme_near_point_additive_action`, with proof `sorry`.
The accepted natural-language statement and proof are unchanged. No new Lean definitions or dependency repairs are needed. The H2 repair adds the
owning definition node `def-per-normal-cone-fibre-piece` for the existing degree-piece
construction, without copying its Lean definition. The theorem docstring includes all six
proof steps, including the nonminimal-presentation reduction and empty kernel case.

Hypothesis and clause correspondence:

- Arbitrary ground field: `{F : Type v} [Field F]`, with no characteristic restriction.
  Local commutative Noetherian F-algebra: `{R : Type u} [CommRing R] [IsLocalRing R]
  [IsNoetherianRing R] [Algebra F R] [Algebra.EssFiniteType F R]`. The `IsLocalRing`
  class includes nontriviality, so no duplicate `Nontrivial R` instance is required.
  The ground field and algebra have independently explicit universes.
- Prime centre contained in the maximal ideal: `(I : Ideal R) [I.IsPrime]` and
  `hI : I ≤ IsLocalRing.maximalIdeal R`.
- Regular local quotient: `[IsRegularLocalRing (R ⧸ I)]`, using the ring clause of
  `def-weil-regular-scheme`'s Mathlib match. No regularity of R is assumed.
- Non-component condition: `hcomponents : ∀ p ∈ minimalPrimes R, ¬ I ≤ p`.
- Flat associated graded algebra: `[Module.Flat (R ⧸ I) (Ideal.associatedGraded I)]`.
- Residue field k and fibre S: `IsLocalRing.ResidueField R` and the existing
  `Ideal.normalConeFibre I hI`. This is k tensor_A G, canonically isomorphic by tensor
  symmetry to the node's G tensor_A k. Its scalar map is exactly `Ideal.Quotient.factor hI`.
- The graded pieces are the existing `Ideal.normalConeFibrePiece I hI n`, the k-span
  of the initial classes `1 tensor [a]` for a in I^n. The explicit `GradedAlgebra`
  instance is on these fixed, canonical pieces. This supplies the decomposition
  structure required by Mathlib's Proj; it neither changes the pieces nor asserts
  standardness or flatness beyond the stated hypotheses. These pieces canonically
  form a grading: their split direct-sum decomposition survives tensoring and
  multiplication is induced by multiplication of representatives. Any grading
  decomposition on the fixed pieces is the inverse of the same sum-of-inclusions.
- Blowup and closed-fibre point: `y : AffineBlowup I` and
  `hy : AffineBlowup.toSpec I y = IsLocalRing.closedPoint R`.
- Identification of that fibre with Proj S: `t : Proj (Ideal.normalConeFibrePiece I hI)`
  together with `hpoint`. For every n and a in I^n, membership of `1 tensor [a]`
  in t's homogeneous prime is equivalent to membership of `a T^n` in y's Rees
  homogeneous prime. Thus this is precisely the canonical correspondence. There is
  no arbitrary map or isomorphism parameter. Indeed both degree-n fibre algebras
  are I^n / m I^n because I^(n+1) is contained in m I^n; the displayed representative
  rule is the canonical ring identification and respects multiplication. On a standard
  open the same rule identifies the degree-zero localizations and hence residue fields.
  Because both primes are homogeneous, specifying all homogeneous representatives
  specifies the point completely, including nonclosed scheme points.
- Local ring R_y, its maximal ideal, and h_y: the existing `localFunction (AffineBlowup I) y`.
  Its definition is the length of the indicated quotient, converted to a natural number.
  h_R is `(Module.length R (R ⧸ maximalIdeal R ^ (n+1))).toNat`. These lengths are finite:
  R is Noetherian local, its affine blowup is Noetherian, and its stalk at y is Noetherian
  local. Thus `toNat` loses no information, including at n=0.
- Delta is `Cardinal.toNat (Algebra.trdeg k ((Proj ...).residueField t))` for the canonical
  k-algebra map `Proj.toSpecOfAlgebra ... |>.residueFieldAlgebraMap t`. The representative
  identification above identifies this residue field with kappa(y) as a k-algebra.
  It has finite transcendence degree, since the fibre is of finite type over k.
- Lambda and near equality: the existing inclusive `summation` and its delta-fold
  function iterate; `hnear` states equality with the raw h_R sequence, not a normalized
  or degreewise-inequality substitute. At delta=0 the iterate is the identity.
- Any finite-variable graded surjection: `(N : ℕ)`, the k-algebra homomorphism `π`,
  `hπ : Function.Surjective π`, and `hgraded` saying each degree-n polynomial maps
  to the fixed degree-n piece. There is no minimality or degree-one injectivity hypothesis.
  K is literally `RingHom.ker π.toRingHom`.
- The inverse-image homogeneous prime q_y is literally
  `Ideal.comap π.toRingHom t.asHomogeneousIdeal.toIdeal`.
- The conclusion existentially quantifies an ordinary ideal L, requires `L ≠ ⊤`,
  Mathlib's `Ideal.IsHomogeneous` for total degree, and `L ≤ q_y`.
  The explicit `MvPolynomial.gradedAlgebra` argument supplies the canonical grading
  without a file-local instance or notation.
- Disjoint tuples are indexed by `Fin N ⊕ Fin N`. `rename Sum.inl` and `rename Sum.inr`
  induce the ring maps used by `Ideal.map`; their images are exactly L(Z), L(W), K(Z).
- For every f in L: evaluation at all-zero variables is zero; `aeval (-X ∘ Sum.inl)`
  belongs to L(Z); `aeval (X ∘ Sum.inl + X ∘ Sum.inr)` belongs to L(Z)+L(W).
  Inversion is evaluated in the larger polynomial ring as permitted by the node's
  convention for L(Z).
- For every g in K: that same addition substitution belongs to K(Z)+L(W).
  All statements are polynomial ideal membership, not equality only on rational points.
  No linear-generation claim and no reducedness assumption is present.

Dependency declarations read and reused:

- `Mathlib.RingTheory.EssentialFiniteness`: `Algebra.EssFiniteType`.
- `Mathlib.RingTheory.Noetherian.Defs`: `IsNoetherianRing`.
- `Sheaf.AlgebraicGeometry.IsRegularScheme` and its Mathlib ring match
  `Mathlib.RingTheory.RegularLocalRing.Defs`: `IsRegularLocalRing`.
- `WeilConjectures.RingTheory.AssociatedGradedRing`: `Ideal.associatedGraded`,
  `Ideal.associatedGradedPiece`, and its quotient algebra structure.
- `Mathlib.LinearAlgebra.TensorProduct.Defs`: `TensorProduct`; the existing canonical
  fibre module supplies its ring and scalar structures without duplicating them.
- `Mathlib.RingTheory.RingHom.Flat` / `Mathlib.RingTheory.Flat.Basic`:
  `RingHom.Flat`, `Module.Flat` (the latter states the graded algebra's flatness).
- `Mathlib.AlgebraicGeometry.Scheme`: `Spec`; `WeilConjectures.Blowup.Affine.Defs`:
  `AffineBlowup`, `AffineBlowup.toSpec`, and `reesMonomial` from its Rees grading import.
- `Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Basic`: `Proj` and its homogeneous primes.
- `Mathlib.RingTheory.Length`: `Module.length`.
- `Mathlib.RingTheory.AlgebraicIndependent.Basic`: `Algebra.trdeg`.
- `Mathlib.AlgebraicGeometry.ResidueField`: `Scheme.residueField`; the canonical
  ground-field embedding is `Scheme.Hom.residueFieldAlgebraMap` from
  `WeilConjectures.ZetaSeries`.
- `Mathlib.Algebra.MvPolynomial.Basic` / `Eval` / `Mathlib.RingTheory.MvPolynomial.Homogeneous`:
  `MvPolynomial`, `aeval`, `eval`, `rename`, `homogeneousSubmodule`, `gradedAlgebra`.
- `WeilConjectures.RingTheory.GradedAlgebra.Standard`: the recorded standard-algebra
  framework, also a stated proof dependency. No extra standardness hypothesis is imposed.
- `Mathlib.RingTheory.Localization.AtPrime.Basic`: recorded proof dependency
  `Localization.AtPrime`, imported for the step-3 local map.
- Statement dependencies `def-trf-normal-cone-residue-fibre`,
  `def-per-normal-cone-fibre-piece`, `def-trf-hilbert-samuel-invariant` own,
  respectively, `Ideal.normalConeFibre` and its canonical scalar structures,
  `Ideal.normalConeFibrePiece`, and `HilbertSamuel.summation` / `localFunction`.
  Their modules are public imports; no theorem from the first two is assumed.

The two genuinely unstated proof-only nodes
`lem-per-scheme-near-point-order-generators` and
`lem-trf-projective-order-algebra-additive-generators` have no module to import.
Their interfaces are not required to state the present theorem and are described in
its proof docstring; no proof-only node was silently turned into a hypothesis.

Edge cases checked: every characteristic, including 2 and inseparable residue extensions;
nonreduced R; n=0 and delta=0; nonclosed y; I=m; I=0 (excluded by the non-component/point
hypotheses rather than by an additional restriction); N=0 (the projective-point and graded
surjection data cannot then hold, but no positive-variable hypothesis was added); K=0 and
nonminimal presentations with redundant variables; empty kernel generating family.

Searches before writing:

- `msearch.py ... leanfinder "Hilbert Samuel near point of blowup homogeneous additive
  subgroup translation action on normal cone fibre"` and a shorter equivalent query:
  eight hits on Proj coordinate descriptions and ordinary open additive subgroups; none
  states the near-point theorem.
- `msearch.py ... loogle "MvPolynomial, ProjectiveSpectrum"`: zero hits.
- `msearch.py ... grep "near.?point|directrix|normal.?flat|HilbertSamuel" RingTheory`
  and `"near.?point|directrix|normal.?flat"`: zero hits in Mathlib RingTheory.
- `rg` on `lean/WeilConjectures` and `lean/Sheaf` for near-point, directrix, normal-cone
  fibre, Hilbert--Samuel and translation names: found the canonical fibre and piece
  constructions above and characteristic-zero/reduced stronger normal-cone conclusions;
  no exact theorem. The reduced sister node has no Lean declaration.
- `rg` on `dag/lean_names_upstream.json`, Mathlib and both project source roots for
  `scheme_near_point_additive_action`: no collision.
- `rg -n "lem-per-scheme-near-point-additive-action" lean/WeilConjectures`: no hit.

Source verification: opened [CJS, March 12 2009 preprint](https://epub.uni-regensburg.de/13766/1/MP32.pdf),
printed pp.32--36, in particular the proof of Theorem 2.14. The proof distinguishes
its characteristic-independent subgroup action from the additional conditions making
that subgroup linear. This delivery states only the former. The theorem is not a unit's
own statement and requires no correction or STATEMENT-DISPUTED flag.

Validation: prescribed `scompile.py` passed the sandbox and library-module compiles
without errors or warnings. A first compile exposed the missing explicit polynomial
grading and a redundant `Nontrivial R` instance; both were repaired. The theorem proof
is `sorry`, and there are no other declarations or definitions in the delivered module.

## Second reading by Q130

I reread the node and the completed file clause by clause after compilation. This is a
self-check, not a claim that another worker was started: the dispatcher explicitly forbids
starting other agents and supplies the maintainer's independent review after delivery.
The four local-algebra assumptions are all present and no reducedness assumption appears.
The residue-fibre uses the preexisting tensor model and exact existing pieces. The hpoint
condition fixes the Rees/projective correspondence, so an unrelated scheme point cannot be
substituted. The numerical exponent uses its canonical k-algebra residue field, and finite
length makes the natural-valued formulation equivalent. The arbitrary presentation allows
redundant variables and N=0. The output contains exactly properness, homogeneity, containment
in q_y, zero, inversion, addition, and translation of the kernel equations. The larger
polynomial ring uses disjoint Sum indices throughout; inversion lands in L(Z), whereas
addition lands in L(Z)+L(W) and the kernel clause in K(Z)+L(W). No K≤L clause or linearity
conclusion was added. The compile-driven fixes changed only elaboration and removed a
redundant typeclass binder, without changing the mathematical statement.


## New nodes

`def-per-normal-cone-fibre-piece` owns the existing definition
`Ideal.normalConeFibrePiece` in `Sheaf.RingTheory.NormalFlatHilbertConvolution` using
an `existing: true` record. For a commutative local R, I inside its maximal ideal,
and j in ℕ, it is precisely the k-submodule spanned by the canonical degree-j
initial classes in the normal-cone residue fibre. The signature and body were read
from lines 36–39 of the existing source. Its only statement dependencies are the
existing residue-fibre construction and the submodule-span definition. There is no
Noetherian, flat, reduced, characteristic or finite-dimensionality hypothesis.
At j=0 it spans the degree-zero scalar image; at I=0 its positive pieces are zero.
No grading-instance construction or theorem is added: the reviewer's comment about
supplying an instance was advisory and the returned Lean interface was accepted.

Source: the associated-graded and tensor construction, Stacks Section 00JM and the
proof of Lemma 05GH; the current declaration's docstring also cites Hironaka (1970),
section 2, p.153. Mathlib searches (LeanSearch, LeanFinder and grep) are preserved
verbatim in the new node's `mathlib_searches`. LeanSearch returned Rees, span-power,
Weierstrass and cotangent declarations; LeanFinder returned general graded generation
and homogeneous-localization declarations. Neither supplies this specialized piece.
Mathlib grep returned no exact names. Project grep found exactly the existing
span construction. DAG and blueprint searches found no owning definition node:
`def-trf-normal-cone-residue-fibre` owns the fibre and initial classes, but not this
subspace. Thus the new node records the exact existing definition instead of
introducing a second one.

## Returned delivery repair

H2, immutable returned head `4b58fa1cc37a`: removed the theorem node
`lem-trf-normal-flat-hilbert-convolution` from the item's `stmt_deps` and replaced
it with `def-per-normal-cone-fibre-piece`. The item's module still imports
`Sheaf.RingTheory.NormalFlatHilbertConvolution` because that is where the existing
definition lives; its theorem conclusion is neither used nor assumed. The new
node's `existing: true` record is exactly the correction requested by the reviewer.
The item's Lean text is unchanged from the returned delivery. The item node was
rebased by retaining all current-main fields except the authorized `lean` and
`stmt_deps` fields; the current-main and returned sandbox differed only in these
fields before this repair. No statement correction or citer audit is necessary.

Repair self-reading by Q130: reread the new node, existing signature and span body,
and the item's use of the degree pieces. Every parameter matches the definition;
there is no theorem hypothesis or theorem conclusion in the new definition node.
The item now reaches the fibre construction through its own definition node and
the degree-piece construction through this new definition node. The previously
accepted clause-by-clause statement and edge-case checks above continue to hold.
