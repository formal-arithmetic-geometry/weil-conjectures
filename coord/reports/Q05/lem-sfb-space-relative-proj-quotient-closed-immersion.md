## Worker report

Delivered module: `Sheaf.AlgebraicGeometry.SpaceRelativeProjQuotientClosedImmersion`.
Main declaration:
`AlgebraicGeometry.AlgebraicSpace.space_relativeProj_quotient_closedImmersion`.

The theorem states existence of the system of uniquely characterized quotient arrows for
any of the already supplied relative-Proj scheme-test realizations. Its only postponed
proof is the named main theorem, with all seven DAG proof steps in its docstring.
`spaceProjQuotientSchemeMap` has real data: it is the existing upstream `relProjMap`,
with its existing structural-map equation used to regard it as a morphism over S.
`IsSpaceProjQuotientMap` and `SpaceProjQuotientSystem` only package the clauses of this
node's conclusion; neither introduces another relative Proj, tensor pullback, algebra,
quasi-coherence predicate, homogeneous algebra homomorphism, or closed-immersion predicate.
These helpers belong to this node and are all listed in `lean.declarations`.

Hypothesis and conclusion audit:

| Node clause | Lean rendering |
| --- | --- |
| Scheme S, algebraic space X over S, size convention | Explicit `universe u`, `{S : Scheme.{u}}`, and `{X : AlgebraicSpace S}` throughout. The established algebraic-space model uses `(Over S)ᵒᵖ ⥤ Type u`; no new size equality or smaller test universe is imposed. |
| Graded commutative unital O_X-algebras A and B | Existing `A B : SpaceProjInput X`; its `piece` and `algebra` are exactly the existing component module sheaves and `EtaleGradedModuleAlgebra`. No condition A_0 = O_X is imposed. |
| Every homogeneous piece quasi-coherent | Existing `SpaceProjInput.quasiCoherent : ∀ n, (piece n).IsQuasicoherent`, using the recorded Mathlib predicate specialized by `AlgebraicSpaceQuasiCoherentModule`. |
| Homogeneous unital algebra map φ | Existing `EtaleGradedModuleAlgebra.Hom A.algebra B.algebra`, whose `degree`, `mul`, and `unit` are precisely the degreewise module maps and product/unit equations. |
| Surjectivity in every degree, including zero | `hφ : ∀ n : ℕ, Epi (φ.degree n)`. Epimorphisms in sheaves of modules mean sheaf surjections, not the stronger surjectivity on sections of every chart. |
| Write P_X(A), P_X(B) with scheme-test comparisons | Existing `C : SpaceProjCoefficients S`, `R : SpaceProjSystem C`, and `(R.realization A/B).space`, `.projection`, `.compare`, and `.cartesian`. The dependency theorem supplies these data. The present theorem applies to every such realization, without adding a hypothesis on A or B. |
| Unique arrow r_φ from P_X(B) to P_X(A) | `SpaceProjQuotientSystem.map` supplies the arrow, `specification` asserts its scheme-test characterization, and `unique` states that any arrow with that characterization equals it. Uniqueness does not assume that a competing arrow is already a closed immersion. |
| Arrow is over X | First conjunct of `IsSpaceProjQuotientMap`: `r ≫ projection A = projection B`. |
| Every S-scheme W and arbitrary map g:W to X | Universal quantifiers `(W : Over S) (g : schemeSpace W ⟶ X)` in `IsSpaceProjQuotientMap`. Neither etaleness nor flatness is assumed. |
| Tensor-pulled φ is degreewise surjective | The first conjunct for each W,g is `∀ n : ℕ, Epi ((moduleTensorPullback g).map (φ.degree n))`, using the recorded tensor pullback itself. |
| Passage to the Zariski graded algebra | The map `f : (C.scheme A W g).affine ⟶ (C.scheme B W g).affine` is normalized on every homogeneous affine section by `C.scheme.sections` and the actual `(evaluationZariskiRestriction W).map ((moduleTensorPullback g).map (φ.degree n))`. Thus it cannot be an unrelated graded map. These sections are linear equivalences; equality on all homogeneous sections specifies the full graded map. |
| Induced scheme relative-Proj morphism on the test | The final equation is `compare B ≫ r.hom.hom = yoneda.map (spaceProjQuotientSchemeMap W f hf) ≫ compare A`. The helper unfolds to the existing `Scheme.GradedAlgebraData.relProjMap f (irrelevantLE_of_surjective f hf)`. The existing cartesian comparison squares show this equation says exactly that the base-changed r is the specified scheme map under both comparisons. |
| Surjective affine-section graded ring maps | `hf : ∀ V, Function.Surjective (f.app V)` is part of the test conclusion. It follows from homogeneous sheaf surjections and quasi-coherence on affine opens, not an extra input hypothesis. |
| Representable by schemes and every scheme base change a closed immersion | `closedImmersion : IsRepresentableWith (fun _ _ p ↦ IsClosedImmersion p.left) (map φ hφ).hom.hom`. Unfolding the existing `IsRepresentableWith` quantifies over every scheme T and map h_T to P_X(A), producing a representing scheme U, its projection p, a cartesian presheaf square, and `IsClosedImmersion p.left`. Forgetting the last property is precisely `IsRepresentable`; representability is not assumed in advance. |
| Affine etale chart U=Spec R | This is included by taking W=U and g=u in the scheme-test clause. For etale u, the normalized tensor restriction identifies the homogeneous sections with A_n(U), B_n(U). The `SpaceProjSchemeAlgebra.sections` equivalences respect products, unit, and restriction, so its affine graded algebra is the direct sum of those homogeneous section modules. `relProjMap` restricts on the top affine open to the ordinary `Proj.map` of that same graded ring map, by upstream `relProjι_relProjMap`. Thus the stated chart immersion is exactly Proj(B(U)) to Proj(A(U)); no commutation of sections with infinite sheaf coproducts is assumed. |
| Identity | Field `identity`, for a homogeneous map with every `degree n = 𝟙 (A.piece n)`, says `map φ hφ = 𝟙 (R.realization A).space`. Identity homogeneous maps have those components, including degree zero. |
| Composition of surjections | Field `composition`, for χ with `χ.degree n = φ.degree n ≫ ψ.degree n`, says `map χ hχ = map ψ hψ ≫ map φ hφ`. The component equalities express precisely χ=ψ∘φ; the composite surjectivity is automatic from the two epi hypotheses. This componentwise formulation uses the existing Hom structure rather than privately redefining its identity/composition operations. |
| Empty Proj spaces allowed | There is no nonemptiness, chosen point, positive-rank, nontrivial-ring, or finite-generation premise anywhere. All conclusions are morphisms and equalities valid for empty sources and targets. |

Dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme`, scheme morphisms.
- `Sheaf.AlgebraicGeometry.AlgebraicSpace`: `AlgebraicGeometry.AlgebraicSpace`,
  `AlgebraicSpace.IsRepresentableWith`, `IsRepresentable`, and the scheme-test model.
- `def-weil-size-convention` is a recorded metatheoretic convention, with no module
  or declaration; it is rendered by the explicit universe and the existing site's sizes.
- `Sheaf.TraceFormula.EtaleGradedModuleAlgebra`:
  `AlgebraicSpace.EtaleGradedModuleAlgebra`, `.Hom`.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceQuasiCoherentModule`:
  `AlgebraicSpace.QCoh`, its slice-instance support, and the reused
  `SheafOfModules.IsQuasicoherent` predicate.
- `Sheaf.AlgebraicGeometry.SpaceRelativeProjSchemeTests`:
  `SpaceProjInput`, `SpaceProjCoefficients`, `SpaceProjSystem`, `SpaceProjRealization`,
  `SpaceProjSchemeAlgebra`, `spaceProjScheme`, and
  `exists_space_relativeProj_scheme_tests`, all in `AlgebraicGeometry.AlgebraicSpace`.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceModuleOperations`:
  `AlgebraicSpace.moduleTensorPullback` (the left adjoint to the specified section-limit
  direct image), its adjunction and normalized tensor sections.
- `WeilConjectures.AlgebraicGeometry.RelativeProj.Functoriality`:
  `Scheme.GradedAlgebraData.relProjMap`, `irrelevantLE_of_surjective`,
  `relProjMap_relProjHom`, `relProjι_relProjMap`, `isClosedImmersion_relProjMap`.
- `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`: `IsClosedImmersion`.

All statement dependencies' usable declarations are reused, with public imports for
statement interfaces. Recorded proof modules are included as plain imports, including
the tensor compositor, scheme quotient functor, scheme quasi-coherent equivalence,
module pullback adjunction, homogeneous localization, twists, and fibre-product cover
facts. `lem-sfb-space-qcoh-affine-chart-calculus` and
`lem-sfb-space-closed-immersion-atlas-locality` have no recorded module at this read;
they are proof prerequisites only, are named in the full proof docstring, and introduce
no object needed to type this statement. They therefore require no dependency module
in this delivery. No new node, dependency repair, or statement correction was needed.

Edge cases checked before writing and again against the declaration:

- Identity surjection: the induced arrow has the asserted identity, without a chosen
  representative or a freely selected comparison morphism.
- Two surjections and their composite: contravariance has the correct order
  `map ψ ≫ map φ`, which represents r_φ composed with r_ψ.
- A=0, B=0, and algebras concentrated in degree zero: empty relative Proj is allowed.
- Quotient of a polynomial algebra by its positive-degree ideal: the empty source maps
  to the possibly nonempty target. A map to empty target forces source empty; nothing
  in the interface excludes this.
- Generators in degrees greater than one: no generation-in-degree-one assumption.
- Degree-zero piece different from O_X and degree-zero surjection: retained explicitly.
- Arbitrary non-flat scheme tests, non-quasi-compact X or W, non-Noetherian bases,
  and empty base schemes: no extra restrictions.

Searches (2026-10-24; msearch wrapper records the original queries/results):

- LeanFinder: “A degreewise surjective graded quasi-coherent algebra homomorphism induces
  a unique closed immersion of relative Proj algebraic spaces compatible with scheme
  tests and composition”. Eight hits, including `Proj.fromOfGlobalSections`,
  `Proj.pullbackAwayιIso`, and valuative-criterion facts; none is the space statement.
- Loogle: `AlgebraicGeometry.Proj.map, AlgebraicGeometry.IsClosedImmersion`.
  Zero hits.
- msearch grep in Mathlib/AlgebraicGeometry:
  `isClosedImmersion.*[Pp]roj|[Qq]uotient.*[Pp]roj`. Zero hits.
- LeanSearch: “Surjective graded quasi-coherent algebra homomorphisms induce closed
  immersions on relative Proj algebraic spaces”. Eight hits: the scheme closed-immersion
  predicate and Spec surjection facts, with no relative-Proj space statement.
- Direct rg searches for surjection/Proj/closed-immersion and the proposed names in
  Mathlib's ProjectiveSpectrum, `lean/WeilConjectures`, `lean/Sheaf`, and
  `dag/lean_names_upstream.json`: the upstream scheme theorem is available and reused;
  the scheme-test module has only algebra-isomorphism functoriality. No duplicate of
  the present quotient-space statement or its conclusion helpers was found.
- Exact item-id grep in `lean/WeilConjectures`: no occurrence.

Sources checked directly: `literature/stacks-project/spaces-divisors.tex`, the full
085F/085G/085H lemma and proof text, and the latest blueprint's
`sec-six-functors-basics/sk-thm-sf-ctf-stability/_section.md`.
The undefined R in Stacks 085H(2) is its existing typographical P/R slip; the node
already correctly gives the map Q to P. No alteration of the node is necessary.
The supplied CompactObject example module is now withdrawn; its recorded upstream
binding was read, and the current module format follows the existing scheme-test module.

Validation: the prescribed scompile wrapper compiled the delivered file both as its
sandbox and library module against the live server, cleanly (21.5 s and 5.2 s).
All definitions contain real data; the sole theorem proof is `sorry` as required for
stage 2. Node changed only in `lean`; all universes and variables are explicitly bound.

Delivery dry run: `deliver2.py Q05 lem-sfb-space-relative-proj-quotient-closed-immersion --no-push` passed server preflight and per-file compilation (dry-run commit 544ac206c3d).

## Second reading by Q05

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
