## Worker report

The module `Sheaf.AlgebraicGeometry.StrictTransformComparisonEpimorphism` states
`AlgebraicGeometry.Scheme.Modules.successiveModuleStrictTransform_comparison_epimorphism`.
Its only theorem proof is `sorry`. Five auxiliary definitions give the actual successive
transform, its composite quotient, the canonical base-change identification, the transported
single transform, and its canonical quotient. They have real data and source/blueprint
docstrings. No new DAG nodes or dependency repairs are required. No statement correction
or statement dispute is needed.

Source read: Stacks `divisors.tex`, Tag 080I,
`lemma-strict-transform-composition-blowups`, especially the first two proof paragraphs,
and Tag 080D, `definition-strict-transform` (1) and its preceding paragraph. The requested
comparison is the factorization in those paragraphs, not the later injectivity result.

Hypothesis and object correspondence:

- Schemes S and X, and the unrestricted morphism f, are `{X S : Scheme.{u}} (f : X ⟶ S)`.
  No separation, finiteness or flatness condition is imposed on f or X.
- The finite-type quasi-coherent ideal I is `(I : S.IdealSheafData)` with
  `[I.toModules.IsFiniteType]`. `IdealSheafData` is the existing affine-local encoding
  of a quasi-coherent ideal. The first blowup b is exactly `I.blowupMap`, with domain
  `I.blowup`. This retains the specified centre.
- J is `(J : I.blowup.IdealSheafData)` with `[J.toModules.IsFiniteType]`;
  c is exactly `J.blowupMap`, with domain `J.blowup`.
- K is `(K : S.IdealSheafData)` with `[K.toModules.IsFiniteType]`.
  The specified blowup identification is `(e : J.blowup ≅ K.blowup)`;
  `he : e.hom ≫ K.blowupMap = J.blowupMap ≫ I.blowupMap` says it is over S.
- The equality of centre subsets is exactly
  `hK : (K.support : Set S) = (I.support : Set S) ∪ I.blowupMap '' (J.support : Set I.blowup)`.
  Here `support` is the closed subset V of an ideal.
- The arbitrary quasi-coherent module is `(F : X.Modules) [F.IsQuasicoherent]`.
- X1 is `Limits.pullback f I.blowupMap`; p and f1 are its fst and snd.
  X2 is the iterated representative
  `Limits.pullback (pullback.snd f I.blowupMap) J.blowupMap`; q and f2 are its fst and snd.
  This is canonically X times_S S2, with no extra assumption or choice.
- The common module H is written as `q* p* F`, using `tensorPullback` twice.
  The canonical composition comparison identifies it with `(q ≫ p)* F`.
- F1 is the recorded `moduleStrictTransform f I F`; F2 is
  `successiveModuleStrictTransform f I J F h₁`, which applies the same recorded
  definition to f1, J and F1. The theorem concludes `∃ h₁ : F1.IsQuasicoherent, ...`;
  quasi-coherence of F1 is a conclusion, never an added hypothesis. The auxiliary
  definition takes that proof because the recorded definition requires the instance.
- `moduleStrictTransformCompositeBaseMap` is the actual pullback lift with components
  q followed by p, and f2 followed by e.hom. Its commutativity proof uses the two
  pullback conditions and he. This is the canonical identification with X times_S Bl_K S.
  `compositeModuleStrictTransform` pulls the recorded K-transform back along this map,
  giving exactly G transported to X2.

Conclusion correspondence:

- `∃ h₁ ...` and the first two conjuncts state quasi-coherence of F1, F2 and G.
- `successiveModuleStrictTransformπ` is precisely `q*(π0) ≫ π1`. Its Epi conjunct
  asserts the claimed surjectivity of alpha.
- `compositeModuleStrictTransformπ` is beta: first identify q*p*F with `(q ≫ p)*F`,
  then with the pullback of the source of the K-quotient, and apply the pulled-back
  K-quotient. The comparisons use the recorded section-normalized adjunction, so
  beta is canonical. Its Epi conjunct is the stated canonical epimorphism.
- The quantification over every open V and section s of H, with
  `alpha.app V s = 0 → beta.app V s = 0`, says exactly ker alpha is contained in
  ker beta as subsheaves. It does not impose global surjectivity on sections.
- `∃! θ : F2 ⟶ G, alpha ≫ θ = beta ∧ Epi θ ∧ ...` states the unique epimorphic
  comparison and its compatibility with both quotients. Composition in Lean is
  written in diagram order. Since alpha is epi, uniqueness among such comparisons
  is equivalent to uniqueness among all maps satisfying the factorization.
- The last clause quantifies over every V and every section s of F2 killed by θ.
  Its image under the unit of `restrictAdjunction U.ι` is zero, where
  `U = (q ≫ p ≫ f) ⁻¹ᵁ K.support.compl`. This is precisely vanishing on
  V intersect (X2 minus D), since `q ≫ p ≫ f = f2 ≫ c ≫ b` by pullback conditions.
  Thus every local section of ker θ is supported on D. The open restriction/direct
  image unit is the existing canonical restriction map, not an arbitrary map.

Recorded dependencies read and used:

- `def-pc-scheme`: `Mathlib.AlgebraicGeometry.Scheme`, `AlgebraicGeometry.Scheme`
  and `Scheme.Hom`, with their full signatures and local-affineness definition.
- `pqf-def-coherent`: `Sheaf.AlgebraicGeometry.CoherentFiniteType`,
  `Scheme.Modules.IsQuasiCoherentFiniteType`; the corresponding existing
  `SheafOfModules.IsQuasicoherent` and `IsFiniteType` components render the separate
  quasi-coherent and finite-type conditions in this item. The finite-type/QC
  conjunction for F is deliberately not imposed because only QC is required.
- `def-nagata-global-blowup`: `WeilConjectures.Blowup.Gluing`,
  `Scheme.IdealSheafData.blowup`, the glued scheme, and `blowupMap`.
- `def-trf-module-strict-transform`: `Sheaf.AlgebraicGeometry.ModuleStrictTransform`,
  `moduleStrictTransform` and its kernel/restriction definitions, reused without changes.
- `def-pc-fibre-product`: `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`,
  `Limits.pullback`, `pullback.fst`, `pullback.snd`, `pullback.lift` and `lift_fst`.
- `def-pc-module-pullback`: `Sheaf.AlgebraicGeometry.TensorPullbackSectionAdjunction`,
  the upstream `tensorPullback` and the recorded `tensorPullbackSectionComp`.
- Proof dependency `lem-trf-strict-transform-sheaf-kernel`:
  `Sheaf.AlgebraicGeometry.ModuleStrictTransformKernel`, `moduleStrictTransformπ` and
  `moduleStrictTransform_properties`. This module is public because its canonical
  quotient is part of the statement's concrete arrows. The other proof dependency,
  `lem-trf-iterated-transform-quotient-support`, has no Lean record at this base;
  its future proof import is omitted. It is only needed in the proof, not to form
  any object in this statement, and the docstring records its full role.

Edge cases checked before writing and again against the final statement:

- F = 0 gives zero quotient modules and the unique map 0 to 0.
- Empty X or empty blowups are permitted; no nonempty hypothesis appears.
- D empty makes the supported kernel condition vanishing everywhere and comparison
  an isomorphism, consistent with both quotients being unchanged.
- D all of X2 gives G = 0; the kernel-support condition on θ then imposes no further
  restriction, as required. The zero ideal/blowup-empty cases remain meaningful.
- A unit ideal gives identity blowup and no first exceptional locus; the definitions
  and the union equality remain literal. No nonzero/proper-ideal restriction occurs.
- No finite type of F, finite presentation, flatness or characteristic is assumed.
- The one arbitrary scheme universe u covers all schemes in a common ambient universe,
  and every variable and universe is explicitly bound (`autoImplicit` and
  `relaxedAutoImplicit` are both false).

Searches for an existing exact statement:

- `msearch.py leanfinder`, query “The iterated strict transform of a quasi coherent
  module under successive blowups surjects onto its strict transform under the
  composite blowup”: eight unrelated results, principally `SurjectiveOnStalks`
  composition/descent and adic-completion quotient results; no module-transform comparison.
- `msearch.py leansearch`, query “successive blowups module strict transform canonical
  epimorphism comparison”: eight results on module quotient epimorphisms, ring
  localization epimorphisms, generating sections and affine-space surjectivity;
  no exact statement or one-line specialization.
- `msearch.py loogle`, query `"strictTransform"`: zero hits.
- `msearch.py grep`, query `strictTransform|strict_transform`, subdirectory
  `AlgebraicGeometry`: zero Mathlib hits.
- `rg -n 'strictTransform|strict_transform|StrictTransform'` over both
  `lean/WeilConjectures` and `lean/Sheaf`: existing scheme strict-transform calculus,
  module strict-transform definitions/kernel theorem and affine pushforward
  comparison, none states this successive-transform epimorphism.
- Targeted rg over those same two source trees for the item id and
  `moduleStrictTransform.*[Cc]omparison|moduleStrictTransform.*[Cc]omp`: no hits.
  The proposed declaration/helper names were also checked against both trees.

Validation: the whole delivered module compiled independently in module mode using
`scompile.py`, in both sandbox and library-name checks, with no errors or unexpected
warnings. The expected sorry is the sole theorem proof. Initial namespace shadowing
of `Limits.pullback` and implicit parameters of `pullback.condition` were repaired.
The prescribed delivery dry run and delivery follow this report.

## Second reading by NJ

The worker reopened the node and final module for a clause-by-clause self-check;
no independent second worker was started, as the dispatcher brief forbids delegation
and the maintainer supplies the independent review. The matching above was checked
against the actual final signature. Particular checks were that h₁ is concluded,
he fixes e over S, hK uses the image b(V(J)), beta uses normalized canonical tensor
comparisons, Epi does not demand sectionwise surjectivity, and the last restriction
unit uses the inverse image of V(K)'s complement. No mathematical mismatch was found
and no source statement was changed. The concrete fibre-product representative and
the direction of both comparison isomorphisms were checked by the successful compile.
