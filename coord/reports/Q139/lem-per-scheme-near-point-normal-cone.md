## Worker report

Stage 2, Q139, 2026-10-24. Delivered module:
`lean/Sheaf/AlgebraicGeometry/SchemeNearPointNormalCone.lean`.
Main declaration: `AlgebraicGeometry.HilbertSamuel.near_normal_cone_nonreduced`.
The second declaration, `AlgebraicGeometry.HilbertSamuel.near_function_iff_raw`, states
precisely the final equivalence between extended and raw near-point equalities.
Both proofs are `by sorry`. The repair adds a definition node recording existing
constructions; it adds no Lean definitions or postponed auxiliary facts.

Read the entire item, every statement dependency and its recorded Lean or Mathlib
interface, the reduced sibling `lem-trf-hilbert-samuel-near-normal-cone` and its module,
and the existing Hilbert--Samuel invariant node and module. Checked the source directly:
[Cossart--Jannsen--Saito, March 12 2009 preprint](https://epub.uni-regensburg.de/13766/1/MP32.pdf),
section 2, pp.28--29 and 36, including its standing assumptions and Theorems 2.2,
2.3 and 2.14. The beginning of section 2 assumes excellent X, without reducedness of X;
the centre is reduced and regular. The characteristic-zero subgroup argument and all
scheme-point quantifiers apply to the present nonreduced variant. Remark 1.41 distinguishes
the component-dependent normalization from the one used in this node.

### Hypotheses and clauses

| Node text | Lean rendering |
| --- | --- |
| X is a scheme of finite type over Q | `X : Scheme.{u}`, structure morphism `i ≫ p`, `[LocallyOfFiniteType (i ≫ p)]` and `[QuasiCompact (i ≫ p)]`. The standard lift `ULift.{u} ℚ` places the ground field in the scheme universe. |
| X is locally closed in a smooth scheme | `P : Scheme.{u}`, `p : P ⟶ Spec (.of (ULift.{u} ℚ))`, `i : X ⟶ P`, `[Smooth p]`, `[IsImmersion i]`. No separatedness, purity or regularity of X is imposed. |
| h is the length of the local maximal-ideal-power quotient | Existing `HilbertSamuel.localFunction X x n` is `(Module.length (X.presheaf.stalk x) ((X.presheaf.stalk x) ⧸ maximalIdeal _ ^ (n+1))).toNat`. Finite type makes this length finite, so `toNat` loses nothing. |
| Inclusive summation Lambda and extended H | Existing `HilbertSamuel.summation f n` sums `Finset.range (n+1)`, and `HilbertSamuel.function p x` applies its `Cardinal.toNat (Algebra.trdeg k (X.residueField x))` iterates. The algebra structure comes from p, not from an arbitrary choice. |
| C is a smooth closed subscheme | `c : C ⟶ X`, `[IsClosedImmersion c]`, `[Smooth (c ≫ i ≫ p)]`. |
| H restricted to C is locally constant | `hconstant : IsLocallyConstant (fun z : C ↦ function (i ≫ p) (c z))`; this is local constancy of the whole sequence, not of finitely many entries separately. |
| pi is the blowup of C | X' is the actual constructed scheme `c.ker.blowup`, pi is `c.ker.blowupMap`. The node's equivalent strict-transform model is not substituted for a different scheme or an arbitrary map. |
| x belongs to C | `z : C` and `x = c z`. A closed immersion identifies the points of C with its image, so this covers every such x. |
| y is over x | `y : c.ker.blowup` and `hy : c.ker.blowupMap y = c z`. |
| Near-point hypothesis | `hnear : function (c.ker.blowupMap ≫ i ≫ p) y = function (i ≫ p) (c z)`. |
| R and I are the local ring and centre ideal | `X.presheaf.stalk (c z)` and the existing `centerStalkIdeal c z`, which is the kernel of `(c.stalkMap z).hom`. For a closed immersion this is exactly the ideal of C in the local ring of X. |
| A and k are the two quotients | A is `X.presheaf.stalk (c z) ⧸ centerStalkIdeal c z`; k is `X.residueField (c z)`, literally the quotient by the maximal ideal. The existing `centerResidueAlgebra c z` factors the residue map through A. |
| G is the actual associated graded ring | `Ideal.associatedGraded (centerStalkIdeal c z)`, the direct sum of the recorded `associatedGradedPiece` quotients, with the canonical A-algebra action. |
| G is A-flat | First conjunct `Module.Flat A G`, with its usual injectivity-preservation meaning. |
| Exceptional fibre is canonically Proj(G tensor_A k) | Existing `normalFibre c z` is `k ⊗[A] G`, the commuted tensor convention. `normalFibreGrade c z n` spans the pure tensors of degree-n pieces. The conclusion supplies its grading, the graded Rees map phi and its exact formula on every `reesMonomial`; it also supplies an affine chart U and the equality hI of the localized centre ideals. `IsPullback` for `Proj.map phi hirr ≫ AffineBlowup.hom ... hI ≫ c.ker.blowupι U`, `Proj.toSpecOfAlgebra`, the blowup map and `X.fromSpecResidueField (c z)` specifies the exceptional fibre. The Rees-monomial formula rules out an arbitrary identification that might move y. |
| There is a standard graded k-algebra B | Existential `B : Type u`, its `CommRing` and `Algebra k B`, a grading `𝓑 : ℕ → Submodule k B`, `[GradedAlgebra 𝓑]`, and `[GradedAlgebra.IsStandard 𝓑]`. This recorded predicate gives finite degree-one generation and degree zero equal to k. |
| Integer e at least one | `r : ℕ` and `1 ≤ r`; nonnegative integers are used since the stated inequality excludes all negative integers. |
| Graded polynomial isomorphism with deg T_i = 1 | `e : normalFibre c z ≃ₐ[k] MvPolynomial (Fin r) B`, and membership in every grade is equivalent to membership in `normalPolynomialGrade 𝓑 r n` after e. This grading gives coefficient degree j plus monomial total degree d. In particular the polynomial variables have degree one. |
| y lies in the closed linear subspace Proj k[T] | Existential `t : Proj (normalFibreGrade c z)` maps to the specified y by the same canonical fibre map. For every positive n and every b in `𝓑 n`, `e.symm (MvPolynomial.C b)` belongs to `t.asHomogeneousIdeal.toIdeal`. Thus the prime contains the extension of B_+; quotienting B by B_+ gives k, so this is exactly the closed projective subspace of the node. It is not just membership after some unspecified automorphism. |
| No rationality or closedness restriction | Both z and y range over all scheme points. The prime-containment clause applies to nonclosed points as well. |
| No reducedness | Neither theorem has `[IsReduced X]` or an equivalent hypothesis. All constructions reused from the reduced module were read and are defined without such a hypothesis. |
| Raw equality and its equivalence with extended equality | `near_function_iff_raw` is an iff with the displayed extended equality on the left and `(summation^[Cardinal.toNat (@Algebra.trdeg ...)]) (localFunction c.ker.blowup y) = localFunction X (c z)` on the right. The algebra instance in the transcendence degree is explicitly `((X.residueFieldCongr hy).inv ≫ c.ker.blowupMap.residueFieldMap y).hom.toAlgebra`. This is the induced extension from kappa(x) to kappa(y), transported along hy. The iff does not assume either equality, and requires no centre constancy because the tower/cancellation calculation does not use it. |

### Dependency declarations used

The following recorded interfaces were opened and reused. Their statements were not replaced.

| Node | Module and declarations |
| --- | --- |
| def-weil-finite-type-morphism | `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`, `AlgebraicGeometry.LocallyOfFiniteType`; `Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact`, `AlgebraicGeometry.QuasiCompact`. |
| def-weil-closed-immersion | `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`, `AlgebraicGeometry.IsClosedImmersion`; the immersion condition is `AlgebraicGeometry.IsImmersion` from `Mathlib.AlgebraicGeometry.Morphisms.Immersion`. |
| def-sbc-smooth-morphisms | `Mathlib.AlgebraicGeometry.Morphisms.Smooth`, `AlgebraicGeometry.Smooth`. |
| def-weil-pbc-module-length | `Mathlib.RingTheory.Length`, `Module.length`, through the existing localFunction. |
| def-kun-transcendence-degree | `Mathlib.RingTheory.AlgebraicIndependent.Basic`, `Algebra.trdeg`. |
| def-weil-residue-field | `Mathlib.AlgebraicGeometry.ResidueField`, `Scheme.residueField`, `Scheme.Hom.residueFieldMap`, `Scheme.residueFieldCongr`. |
| def-nagata-global-blowup | `WeilConjectures.Blowup.Gluing`, `Scheme.IdealSheafData.blowup`, `blowupMap`, `blowupι`. |
| def-nagata-strict-transform | `WeilConjectures.Compactification.StrictTransform`, `AlgebraicGeometry.strictTransform`; intrinsic blowup model is used as permitted by the node. |
| def-weil-pbc-associated-graded-ring | `WeilConjectures.RingTheory.AssociatedGradedRing`, `Ideal.associatedGradedPiece`, `Ideal.associatedGraded`, `Ideal.associatedGradedAlgebra`. |
| def-pc-proj | `Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Scheme`, `AlgebraicGeometry.Proj`, `AlgebraicGeometry.projIsoSpec`; `ProjectiveSpectrum.basicOpen` is in the topology module. The canonical maps are from `WeilConjectures.AlgebraicGeometry.RelativeProj.Affine` and the published Proj functor module. |
| def-weil-pbc-module-tensor-product | `Mathlib.LinearAlgebra.TensorProduct.Defs`, `TensorProduct`; tensor algebra structure from `Mathlib.RingTheory.TensorProduct.Basic`. |
| def-pc-standard-graded-algebra | `WeilConjectures.RingTheory.GradedAlgebra.Standard`, `GradedAlgebra.IsStandard`. |
| def-weil-pbc-mv-polynomial-ring | `Mathlib.Algebra.MvPolynomial.Basic`, `MvPolynomial`; the polynomial grading uses `MvPolynomial.monomial`. |
| def-trf-hilbert-samuel-invariant | `Sheaf.AlgebraicGeometry.HilbertSamuelInvariant`, `HilbertSamuel.localFunction`, `summation`, `function`. |
| def-per-near-point-normal-fibre-constructions | `Sheaf.AlgebraicGeometry.HilbertSamuelNearNormalCone`, its constructions `centerStalkIdeal`, `centerResidueAlgebra`, `normalFibre`, `normalFibreGrade`, `normalPolynomialGrade`. Its reduced theorem is not applied. |

The existing Hilbert--Samuel invariant node and the new definition node
`def-per-near-point-normal-fibre-constructions` are cited in stmt_deps. The latter records
the five plain constructions already present in the reduced theorem module. The theorem
node `lem-trf-hilbert-samuel-near-normal-cone` is not a statement dependency. The item's
statement, proof and proof_deps remain unchanged; no Lean declaration is moved or copied.

The public import provides the statement dependencies, including the affine Rees/blowup
maps. The proof-only imports cover the recorded conormal, regularity, dimension and
relative-Proj results and the Mathlib Noetherian, transcendence-tower, zero-dimensional,
torsion-free and Nakayama inputs. The two new nonreduced local input nodes
`lem-per-bennett-normal-flat-local-criterion` and `lem-per-scheme-near-point-additive-action`
are proof dependencies with no recorded declaration yet, so have no import at this stage;
they are named explicitly, with their required uses, in the proof docstring.

### Edge cases checked

* Empty X or C supplies no z; empty blowup supplies no y. No spurious nonempty assumption
  is made on a scheme independently of the specified points.
* For I=0 the intrinsic blowup is empty. Its absence of y is consistent with the positive
  polynomial factor in the conclusion. Nilpotent I is also handled by the proof's empty
  Proj argument, using a power of I rather than reducedness.
* At n=0 localFunction uses the quotient by m and summation includes the sole index zero.
  This is the length convention of this node, not the degree-zero Hilbert function of gr_m.
* A closed centre point and a nonclosed near point are both allowed. The transported
  residue extension in the raw iff can have positive transcendence degree. When delta=0,
  the summation iterate is the identity, as required.
* For a smooth affine space and a point centre, G is polynomial, B=k is standard graded,
  and every point of the exceptional projective space satisfies the containment of B_+.
  No closedness or rationality of its point is forced.
* The examples Q[t,epsilon]/(epsilon^2), centre (t,epsilon), and
  Q[t,s,epsilon]/(epsilon^2), smooth centre (t,epsilon), retain their nilpotent structure.
  The theorem never replaces their associated graded algebra by that of the reduction.
* All types and universes are explicit (`set_option autoImplicit false`). k is the lifted
  rational field in the scheme universe; the graded algebra and its polynomial ring stay
  in that universe. Finitely generated presentations provide small B in the same universe.

### Searches

The prescribed msearch wrappers were run for this item. Exact machine outputs are in the
sandbox's searches.jsonl (not an extra delivered file).

* LeanFinder: `normal cone at Hilbert Samuel near point of blowup is flat over smooth center
  and splits off polynomial variables without reducedness`. Eight hits, on standard smooth
  algebras, the smooth locus and smooth-flatness; no near-point statement.
* Loogle: `AlgebraicGeometry.HilbertSamuel.near_normal_cone, Module.Flat, Algebra.trdeg`.
  Zero hits; the project-local first identifier is unknown to the Mathlib service.
* Mathlib grep via msearch: `HilbertSamuel|near_normal_cone|normalFibre`, subdirectory
  AlgebraicGeometry. Zero hits.
* LeanSearch: `For a scheme over Q with a smooth center of locally constant Hilbert Samuel
  function, a near point in the blowup lies in a projective linear factor of the normal
  cone, allowing nilpotents`. Eight hits: scheme constructors/local affine structure,
  nilradical and local nilpotence, smoothness/smooth locus, reduced stalks and germ
  injectivity. No normal-cone near-point theorem.
* rg in lean/WeilConjectures and lean/Sheaf for `normal.*cone|Hilbert.*Samuel|associatedGraded|
  IsStandard`, then `near_normal_cone|normalFibre`, plus the exact new declaration names.
  Found the reduced theorem and its reusable constructions; its `[IsReduced X]` means it
  is not an exact match. The normal-bundle/regular-immersion results require a regular
  immersion and do not state this theorem. The new declaration names have no collision.
* `grep -rn 'lem-per-scheme-near-point-normal-cone' lean/WeilConjectures` returned no match.
  The upstream declaration-name index was also searched for the proposed names.
* DAG lookup found the existing Hilbert--Samuel invariant and reduced near-normal-cone
  nodes, whose recorded declarations were opened in full. The item is the separately
  reviewed nonreduced generalization; the older reduced assertion was not redefined.

No STATEMENT-DISPUTED issue or statement correction was needed.

Validation: scompile.py compiled both the sandbox form and the actual library-module form
on the server, against the live published build. Latest run: sandbox 29.2 s, library
8.2 s; no errors or non-sorry warnings. No local Lean compiler or global build was run.

## Second reading by Q139

Separate clause-by-clause self-review, with the node and the final file open. The dispatcher
forbids starting other agents; this is not represented as an independent agent review.
The maintainer's independent review is still required by the assignment.

Rechecked all rows above against the source signature. In particular, the only difference
from the sibling's geometric hypotheses is removal of IsReduced; all underlying definitions
were inspected to ensure they have no reducedness binder. No arbitrary scheme iso or
residue-field algebra action is allowed: the fibre map is fixed on Rees monomials and the
relative residue action is explicitly induced by pi and hy. The raw-near equivalence is
stated without hnear, so it does not just restate a hypothesis. Grade preservation is for
every n and every element, and prime containment is for all positive homogeneous
coefficients, exactly the ideal B_+ extended to the polynomial ring. The universal grade
membership condition includes both directions, so the polynomial isomorphism is graded.
The positivity clause excludes r=0, while allowing B=k. No point is assumed rational or
closed. Both theorem proofs are only sorry and both docstrings cite this node, source and
full relevant proof steps. No mismatches remain after adding the explicit raw iff and
recording the invariant dependency and the dedicated construction definition node.


## New nodes

`def-per-near-point-normal-fibre-constructions` records the five existing declarations
`AlgebraicGeometry.HilbertSamuel.centerStalkIdeal`, `centerResidueAlgebra`, `normalFibre`,
`normalFibreGrade` and `normalPolynomialGrade` in
`Sheaf.AlgebraicGeometry.HilbertSamuelNearNormalCone`, with `existing: true`.
Its statement spells out the stalk kernel I, quotient-to-residue scalar action,
k tensor_A gr_I R, the spans of homogeneous pure tensors, and the polynomial monomial
spans with coefficient degree plus monomial degree equal to n. These match the existing
definitions exactly; the polynomial span definition requires no grading instance.
The source is CJS section 2, pp.29,36. The new node's Lean signature is the exact
centerStalkIdeal signature and lean.declarations lists all five declarations.

The new LeanSearch query about normal-fibre algebras and gradings and LeanFinder query
about normal cone tensor product gradings returned generic graded-tensor constructions,
not these scheme-stalk specializations. Mathlib grep returned zero hits for the four
specific construction names. Searching all DAG nodes found only the reduced theorem
record listing these names, not a definition node owning them. The blueprint search
for normal fibre returned zero matches. The full tool outputs are preserved in the new
node's mathlib_searches. The live project module gives the exact existing match;
no module is added for this definition node. Empty schemes have no z; zero or nilpotent
I is allowed; n=0 and r=0 are allowed in the constructions; arbitrary submodule families
are allowed for the polynomial span. No reducedness or near-point conclusion is assumed.

## Repair of return H2

The independent review of immutable head ec8547f4d35b identified the theorem-node
statement dependency used only to access five plain constructions. Replaced that
dependency with `def-per-near-point-normal-fibre-constructions`, whose existing:true
record lists those exact declarations without moving them. The Lean file is byte-for-byte
unchanged from the returned delivery; both theorem signatures and proofs are unchanged.
Refreshed the item's other fields from the current read-only main node before applying
the authorized lean/stmt_deps delta. No mathematical statement correction was made.

Additional second reading by Q139: read the five existing declaration bodies and the
new definition-node statement together. Kernel, quotient factorization, tensor factors,
homogeneous inclusion, linear spans and the j+d.degree=n equation all match. None of
the definitions invokes or chooses data from near_normal_cone. The item now cites the
definition node instead of that theorem; no other dependencies or Lean imports changed.
This addresses the sole numbered return point H2.
