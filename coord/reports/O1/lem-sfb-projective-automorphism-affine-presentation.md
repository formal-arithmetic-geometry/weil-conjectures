## Worker report

The delivery states `lem-sfb-projective-automorphism-affine-presentation` in
`Sheaf.AlgebraicGeometry.ProjectiveAutomorphismAffinePresentation`. It defines the
polynomial quotient explicitly, and leaves the four named theorem proofs `sorry`.
No node statement or dependency is changed. No new node or dependency repair is needed:
the helper constructions belong to the explicit presentation already specified by this node.

Clause-by-clause comparison:

- The commutative ring is `(A : Type u) [CommRing A]`; the module is
  `(P : Type u) [AddCommGroup P] [Module A P]`. The finite splitting is given by
  `(n : ℕ)`, `i : P →ₗ[A] (Fin n → A)`, `p : (Fin n → A) →ₗ[A] P`, and
  `hpi : p.comp i = LinearMap.id`. This is precisely the supplied direct-summand
  witness, not an additional freeness or rank hypothesis.
- `B ⊗[A] P` is the recorded tensor product. `inclusion` and `projection` are
  `LinearMap.baseChange` composed with `TensorProduct.piScalarRight` and its inverse.
  `projector i p` is the matrix of `i.comp p` on the standard coordinate vectors.
- `genericMatrix` uses variables indexed by `Bool × Fin n × Fin n`. False is U,
  true is V. `relations` lists eU-U, Ue-U, eV-V, Ve-V, UV-e, VU-e in that order.
  `relationIdeal` spans every entry, and `coordinateAlgebra` is its actual quotient.
  There is no choice or postponed proof in these definitions.
- `scheme e` is `algSpec` of this quotient, hence precisely Spec D_e over Spec A.
  `affine_presentation` asserts a `GrpObj` on that object and bijections `φ B`
  from its B-points to B-linear automorphisms of the stated tensor product.
- The displayed coordinate equality, for every algebra homomorphism f and both
  matrix selectors, says the point associated with an automorphism a has
  coordinates `automorphismMatrix i p a` and `automorphismMatrix i p a.symm`.
  That helper is explicitly i_B a p_B on the standard basis vectors.
- The multiplication clause applies `φ` to `CartesianMonoidalCategory.lift x y ≫ g.mul`
  and equates it with `φ B x * φ B y`. Linear-equivalence multiplication is composition.
  The last clause of `affine_presentation` says that for every A-algebra map B→C,
  the induced automorphism intertwines the canonical tensor map with the original one.
  This is scalar extension, including arbitrary nonflat coefficient maps, not a chosen
  unspecified transition. Pure tensors span, so the equality uniquely determines it.
- Finite presentation is `LocallyOfFinitePresentation`, `QuasiCompact`, and
  `QuasiSeparated` on the structure map; the asserted `IsAffineHom` supplies affineness.
- The counit ε is an A-algebra map D_e→A, its value on every coordinate is the
  corresponding entry of e, and `g.one.left` is exactly its Spec. Its Spec is asserted
  to be `IsClosedImmersion`. Its kernel is finitely generated and equals
  `identityIdeal e`, the span of the entries of U-e and V-e.
- `base_change` quantifies over an arbitrary A-algebra B, which encodes any ring
  homomorphism A→B by its induced algebra structure. It uses the actual tensor-extended
  i and p, gives the coefficient map γ, and an isomorphism δ from D_e tensor_A B to
  the new presentation. `IsCoefficientMap` requires the new projector to be e with
  coefficients mapped and γ to fix all named variables and map all coefficients.
  The δ equality characterizes the map on every pure tensor.
- The scheme isomorphism `s` is required to equal `pullbackSpecIso` followed by
  Spec of δ inverse. Its inverse followed by the second projection is the structure
  map. This is the canonical isomorphism over Spec B, not merely an unqualified
  existence of an isomorphic scheme.
- For any two identity evaluations with the specified coordinate values, the counits
  commute with γ. Contravariant Spec is exactly identification of the identity sections.
- The final clause of `base_change` identifies represented automorphisms via
  `TensorProduct.AlgebraTensorModule.cancelBaseChange`. Equality of their matrices
  implies equality of the automorphisms under that canonical comparison. Together
  with the coordinate-normalized representing bijections this states precisely the
  pointwise identification under base change, including the original and inverse maps.
- `coefficient_coherence` says two successive coefficient maps equal the direct map,
  and a coefficient map for the identity ring map equals the identity. These maps fix
  all the generators, so the statement also covers the identity base change.
  `tensor_coherence` says the two cancellation maps on the triple base change agree.
  Thus both the scheme and represented automorphism identifications commute with
  successive changes of base; identity evaluations already commute with each map.

Dependencies read and used: `TensorProduct` in
`Mathlib.LinearAlgebra.TensorProduct.Defs`, its map/base-change constructions in
`Map`, `Pi`, and `Tower`; `AlgebraicGeometry.Spec` and `Spec.map` in
`Mathlib.AlgebraicGeometry.Scheme`; `AlgebraicGeometry.IsClosedImmersion` in
`Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`; `MvPolynomial` in
`Mathlib.Algebra.MvPolynomial.Basic` and evaluation in `Eval`;
`AlgebraicGeometry.LocallyOfFinitePresentation` in
`Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation`; and
`CategoryTheory.Limits.pullback` in
`Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`.
All of these are the current dependency records or their exact Mathlib matches.
The actual Spec-over-base construction is Mathlib `algSpec`, and the group notion
is Mathlib `GrpObj`; neither is copied. The proof imports also cover each stated
proof dependency: affine morphisms, separatedness, affine-spectrum pullbacks,
algebra tensor maps, and finite-presentation and quotient-immersion APIs.
The retired CompactObject example was inspected, along with its current upstream
replacement, for the module header and declaration-record conventions.

Source read: `literature/stacks-project/groupoids.tex`, `example-general-linear-group`
(Tag 022W), including its multiplication and base-change paragraphs. The node's
source explicitly identifies the split-summand extension as the agent argument;
its nine full proof steps were read and transferred to the theorem docstrings.
The latest blueprint provenance was checked; this supporting node is not a unit's
own statement. No source-based correction is needed.

Edge cases checked before writing: n=0 uses Fin 0 everywhere, so both polynomial
matrices and all relation and identity generators are empty, D_e=A and J=0.
P=0 with n>0 gives e=0 and the support relations kill U,V, again yielding A.
No `Nontrivial A`, positive-rank assumption, domain/field assumption, flatness,
constant rank, or `Nonempty (Fin n)` occurs anywhere. The zero ring is permitted.
Changing coefficients to the zero ring remains a permitted arbitrary base change.
Both trivial and nontrivial successive and identity base changes are in scope.

Searches, all before deciding to state the theorem: prescribed msearch LeanFinder
query “The automorphism functor of a finite projective module is represented by an
 affine finitely presented group scheme” returned eight Galois/Tannaka hits, no match;
Loogle `LinearEquiv.baseChange, CategoryTheory.GrpObj` returned zero hits; Mathlib
AlgebraicGeometry grep `generalLinear|automorphism.*scheme|ProjectiveAutomorphism`
returned zero hits. LeanSearch query “The automorphism functor of a finite projective
module is represented by an affine scheme of finite presentation” returned abstract
linear automorphism groups, affine schemes and affine-space finiteness results,
none giving this statement. Direct rg of project and Mathlib for
`projectiveAutomorphism`, idempotent coordinate constructions and projective
module automorphism schemes found no duplicate. GeneralLinear searches did find
finite-free linear-action constructions and StandardGroupSchemes; their signatures
were inspected, and they do not give the arbitrary split-projective construction.
The required upstream grep for this node id found no declaration. The generated
full declaration names were also searched in dag/lean_names_upstream.json.

Validation uses scompile.py exclusively, separately for this module in module mode.
The compiler has accepted the matrix presentation and the base-change/coherence
statements, with no unexpected warning. The final dry run and delivery are performed
with the prescribed deliver2.py wrapper.

## Second reading by O1

This is an author self-check, not a claim of an independent reader: the dispatcher
forbids starting another agent, and independent review belongs to the maintainer.
I reopened the complete node and compared each clause with the finished file as
listed above. The direct-summand witness, both matrix-coordinate formulas,
composition multiplication, arbitrary algebra-map naturality, exact quotient,
finite identity ideal, canonical affine pullback comparison, counit compatibility,
and identity/successive base changes are all present. Helpers have real data;
the only sorries are the four named statements of this same node. No mismatch,
statement dispute, added mathematical hypothesis, missing clause, or node change
was identified. Compiler corrections concerned only equation syntax and making the
quotient type an abbreviation so its canonical ring/algebra instances are visible.

## Maintainer review fix (independent reader, 2026-10-25)

The section above is an author self-check. This is the independent clause-by-clause reading
of the delivery at 1996fda3 against the node, Stacks Tag 022W (groupoids.tex,
example-general-linear-group; free GL_n only, so the split-summand extension is the node's
agent proof) and the recorded Mathlib leaves. No Lean or node record is changed.

Objects and hypotheses:
- A commutative ring: `(A : Type u) [CommRing A]`. Exact.
- P with split maps i : P → A^n, p : A^n → P, pi = 1: `P : Type u`, `i`, `p`,
  `hpi : p.comp i = LinearMap.id`. Exact; no rank, freeness, nontriviality or
  `Nonempty (Fin n)` hypothesis. (P is put in the universe of A; since P ≅ range i ⊆ A^n
  this loses no module up to isomorphism. Advisory only.)
- e = ip: `projector i p j k = i (p (Pi.single k 1)) j`, the (j,k) entry of the matrix of
  i∘p; the relations use matrix products consistently with composition.
- D_e: `relations` lists eU-U, Ue-U, eV-V, Ve-V, UV-e, VU-e (U = selector false, V = true),
  `relationIdeal` spans every entry, `coordinateAlgebra` is the actual quotient,
  `scheme e = algSpec D_e` is Spec D_e over Spec A. Real data, no choice.
- P_B, i_B, p_B: `B ⊗[A] P`, `inclusion`/`projection` = baseChange composed with
  `piScalarRight` (B ⊗ A^n ≅ B^n). Exact.

Conclusion of `affine_presentation`:
- group scheme: `g : GrpObj (scheme e)`, pinned by the identity clause
  (`g.one.left = Spec.map ε`) and the multiplication clause on all B-points;
- representing bijection `φ B`, pinned by the coordinate clause: for every A-algebra map
  f : D_e → B, f(U) = i_B a p_B and f(V) = i_B a⁻¹ p_B with a = φ B (Spec f); every
  Spec B-point over Spec A is Spec f, and a is recovered as p_B U i_B;
- multiplication = composition: `φ (lift x y ≫ g.mul) = φ x * φ y`, and `*` on
  `LinearEquiv` is `g.trans f`, i.e. composition, matching U ↦ U₁U₂;
- transition maps = scalar extension: the naturality clause intertwines
  `TensorProduct.map f id` for every A-algebra map B → C;
- finitely presented: LocallyOfFinitePresentation, QuasiCompact, QuasiSeparated, plus
  IsAffineHom;
- identity section: ε : D_e → A with ε(U) = ε(V) = e, `Spec.map ε` a closed immersion,
  ker ε finitely generated and equal to `identityIdeal` (entries of U-e, V-e).
All true by the node's steps 1-7 (hand-checked: eU=U=Ue, UV=e from pi=1; aa' = pUeVi = 1;
i(pUi)p = eUe = U; ker ε = J since A → D_e/J is surjective).

`base_change` (step 8): γ fixes U,V and maps coefficients (`IsCoefficientMap`, which also
asserts e' = e mapped entrywise — true), δ(t ⊗ b) = γ(t)·b, s = pullbackSpecIso ≫ Spec δ⁻¹
lying over Spec B, the identity evaluations commute with γ, and automorphisms with equal
matrices correspond under `cancelBaseChange` (true: p_C and p'_C, i_C and i'_C agree through
the cancellation). `coefficient_coherence` and `tensor_coherence` (step 9) give successive
and identity base change; maps out of the quotient polynomial ring are determined by
coefficients and generators, and both iterated cancellations send d⊗(c⊗(b⊗x)) to dcb⊗x.

Edge cases: n = 0 (Fin 0: no variables, relations or generators; D_e = A, J = 0);
P = 0, n > 0 (e = 0 forces U = V = 0); the zero ring A or B; varying rank
(A = k×k, e = (1,0)). None is excluded.

One definition per notion: the free GL_n scheme `AlgebraicGeometry.GeneralLinearGroup`
(WeilConjectures/AlgebraicGeometry/GroupScheme/GeneralLinear.lean) and
`Sheaf.AlgebraicGeometry.LinearGroupSchemes` (def-sc-general-linear-group, over a field)
cover only free modules; no split-projective automorphism scheme exists in Mathlib,
side-live Sheaf or WeilConjectures. stmt_deps are all Mathlib leaves used as recorded
(TensorProduct, Spec, IsClosedImmersion, MvPolynomial, LocallyOfFinitePresentation,
pullback). Node record: only the `lean` field differs from the base; `lean.statement`
is verbatim in the file and all 16 listed declarations exist. Docstrings carry the source
place and blueprint id; proofs are `sorry` only; helpers have real data.
