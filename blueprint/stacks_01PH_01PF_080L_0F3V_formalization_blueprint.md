# Formalization blueprint for Stacks tags 01PH, 01PF, 080L, and 0F3V

## Scope and target

This blueprint is aimed at Lean 4/Mathlib and at the Nagata-compactification
development in `weil_conjectures_proof_blueprint.tex`.  The four results form
one dependency chain:

```text
01PF  finite-type extension of a quasi-coherent submodule
  |
  v
01PH  quasi-compact open <-> finite-type ideal cutting out its complement
  |                                  \
  v                                   \
080P  separation of disjoint qc opens  \
  |                                     v
  +-------------------------------> 0F3V(2)
  v                                  ^
0F3V(1) -----------------------------+

080B  composition of arbitrary blow-ups
  |
  v
080L  composition of admissible blow-ups
```

The Stacks sources are:

- [01PH, Lemma 28.25.1](https://stacks.math.columbia.edu/tag/01PH)
- [01PF, Lemma 28.23.2](https://stacks.math.columbia.edu/tag/01PF)
- [080L, Lemma 31.35.2](https://stacks.math.columbia.edu/tag/080L)
- [0F3V, Lemma 38.33.2](https://stacks.math.columbia.edu/tag/0F3V)

The names below are proposed interfaces, not claims that these declarations
already exist in Mathlib.

## 0. Foundation and representation choices

### 0.1 Objects that must be fixed first

Use the following representations consistently.

1. A scheme open is `X.Opens`, not an untyped subset.  For a morphism
   `f : Y ⟶ X`, write `f ⁻¹ᵁ U` schematically for the pulled-back open.
2. An ideal sheaf is represented initially by `X.IdealSheafData`, matching
   current Mathlib.  Add a predicate `IdealSheafData.IsFiniteType` defined
   affine-locally by `Ideal.FG`, and prove that it agrees with finite type of
   the corresponding sheaf of modules once an actual subsheaf interface is
   available.
3. Equality of restricted ideals must be an explicit isomorphism/equality
   transported through restriction, not literal definitional equality.
4. A blow-up should be a scheme over `X`, preferably an object of `Over X`,
   together with its universal property.  Isomorphisms of blow-ups should be
   isomorphisms in `Over X`.
5. Scheme-theoretic strict transform and topological closure must remain
   distinct.  Prove comparison lemmas before passing from one to the other.

### 0.2 Suggested bundled interfaces

Schematic Lean interfaces:

```lean
structure BlowupData (X : Scheme) (I : X.IdealSheafData) where
  obj : Scheme
  π : obj ⟶ X
  exceptionalInvertible : IsInvertible (I.extend π)
  isTerminal : IsTerminal (blowupUniversalProblem X I)

structure AdmissibleBlowup (X : Scheme) (U : X.Opens) where
  center : X.IdealSheafData
  center_finiteType : center.IsFiniteType
  center_disjoint : Disjoint center.support (U : Set X)
  blowup : BlowupData X center
  overOpenIso :
    blowup.obj.restrict (blowup.π ⁻¹ᵁ U) ≅ X.restrict U
```

Stacks tag 080K defines admissibility only as an existential property.  The
bundle above is deliberately stronger.  Store `overOpenIso` only if later
constructions need chosen data; otherwise derive it from the
complement-of-center theorem and avoid coherence obligations.

### 0.3 Common library of micro-lemmas

Before the four target results, establish:

- restriction preserves sums, products, powers, top, and finite type of ideal
  sheaves;
- finite type is preserved by finite sums, products, images, and finitely
  generated submodules;
- `support (I * J) = support I ∪ support J` and
  `V(I + J) = V(I) ∩ V(J)`;
- a closed immersion is of finite presentation iff its ideal is finite type
  ([01TV](https://stacks.math.columbia.edu/tag/01TV));
- finite-presentation closed immersions compose
  ([01TR](https://stacks.math.columbia.edu/tag/01TR));
- affine localization and tilde/restriction comparison for modules;
- gluing of subobjects over a binary open cover, including equality on the
  overlap and the induced inclusion into the ambient object;
- the underlying space of a qcqs scheme is spectral, and an open constructible
  subset of a spectral space is quasi-compact;
- conversions among disjoint supports, empty intersection of closed
  subschemes, and initial/empty fiber product.

## 1. Tag 01PF: extending a finite-type quasi-coherent submodule

### 1.1 Exact statement

Let `X` be qcqs, `j : U ⟶ X` a quasi-compact open immersion, `F` a
quasi-coherent module on `X`, and `G ≤ F|_U` a finite-type quasi-coherent
submodule.  There is a finite-type quasi-coherent submodule `G' ≤ F` whose
restriction to `U` is `G`.

Schematic target:

```lean
theorem exists_finiteType_submodule_restrict_eq
    [IsQuasiCompact X] [IsQuasiSeparated X]
    (j : U ⟶ X) [IsOpenImmersion j] [IsQuasiCompact j]
    (F : X.Modules) (G : Subobject (F.restrict j))
    (hGqc : IsQuasicoherent G) (hGft : IsFiniteType G) :
    ∃ G' : Subobject F,
      IsQuasicoherent G' ∧ IsFiniteType G' ∧
      (restrictSubobject j G' ≅ G)
```

### 1.2 Proof decomposition

#### A. Arbitrary quasi-coherent extension (Stacks 01PE)

Prove first that a quasi-coherent submodule `G ≤ F|_U` has some
quasi-coherent extension `H ≤ F`, without finite-type control.

One construction is

```text
H = ker(F -> j_*((F|_U)/G)).
```

Required lemmas:

1. pushforward by a quasi-compact open immersion into a quasi-separated
   scheme preserves quasi-coherence;
2. kernels and quotients in scheme modules preserve quasi-coherence;
3. restriction to an open is exact;
4. the counit `j^* j_* G -> G` is an isomorphism;
5. the restricted kernel identifies with `G` as a subobject of `F|_U`.

This packages [01PE](https://stacks.math.columbia.edu/tag/01PE), which the
Stacks proof of 01PF invokes in the affine case.

#### B. Affine finite-generation lemma

For `X = Spec R`, write `F = M~` and the extension `H = N~` with `N ≤ M`.
Because `G = H|_U` is finite type, every point of `U` has a principal
neighbourhood `D(f)` on which `N_f` is finitely generated.  Quasi-compactness
of `U` gives a finite cover `U = ⋃ D(f_i)`.  Choose finite generating lists

```text
x_{i1}/f_i^N, ..., x_{ir_i}/f_i^N
```

for the localized modules, after replacing denominators by a common power for
each finite list.  Let `N' ≤ N` be generated by all numerators `x_ij`.  Then:

1. `N'` is finitely generated;
2. `N'_f_i = N_f_i` for every `i`;
3. therefore `N'~|_U = N~|_U = G`;
4. the inclusion `N' ≤ N ≤ M` yields the desired affine subobject of `F`.

Do not hide the following algebra:

- clearing finitely many localization denominators;
- equality of submodules checked on the finite principal cover;
- tilde of a finitely generated module is a finite-type sheaf and conversely
  ([01PB](https://stacks.math.columbia.edu/tag/01PB)).

#### C. Reduction from qcqs to affine

Choose affine opens `V₁, ..., Vₙ` such that

```text
X = U ∪ V₁ ∪ ... ∪ Vₙ.
```

Induct on `n`.  The one-affine step is:

1. `U ∩ V` is quasi-compact by quasi-separatedness;
2. apply the affine result to `(V, U ∩ V, F|_V, G|_(U∩V))`;
3. glue the result on `V` to `G` on `U` using the specified equality on the
   overlap;
4. prove the glued object embeds into `F` and is quasi-coherent and finite
   type (both are local properties).

The induction should use a finite list/Fin index, not “choose a minimal
number” unless minimality is actually needed.  It is not needed.

### 1.3 Extracted declarations

Recommended declaration sequence:

1. `quasicoherentSubmoduleExtension` (01PE(2));
2. `exists_finset_principal_cover_of_finiteType_restrict`;
3. `Submodule.exists_fg_eq_localization_on_finset`;
4. `exists_finiteType_submodule_affine`;
5. `glueSubobject_binaryOpenCover`;
6. `exists_finiteType_submodule_restrict_eq` (01PF);
7. ideal specialization with `F = O_X`.

### 1.4 Completion tests

- On an affine scheme the proof reduces to equality of localized submodules.
- Restricting the returned monomorphism to `U` gives the original
  monomorphism, not merely an abstract isomorphic module.
- The ideal specialization proves closure under multiplication by `O_X`, not
  just that the result is an additive subsheaf.

## 2. Tag 01PH: quasi-compact opens and finite-type complement ideals

### 2.1 Exact statement

For a qcqs scheme `X` and an open `U`, the following are equivalent:

1. `U` is retrocompact in `X`;
2. `U` is quasi-compact;
3. `U` is a finite union of affine opens;
4. some finite-type quasi-coherent ideal `I ≤ O_X` satisfies
   `X \ U = V(I)` set-theoretically.

Formalize the equivalence as a theorem or four named implications, with a
small public theorem for the direction used by 0F3V:

```lean
theorem exists_finiteType_ideal_zeroLocus_compl
    (U : X.Opens) (hU : IsCompact (U : Set X)) :
    ∃ I : X.IdealSheafData,
      I.IsFiniteType ∧ I.support = (U : Set X)ᶜ
```

### 2.2 Proof of `(1) <-> (2) <-> (3)`

Split the Stacks reference to 054D into explicit facts:

1. in a quasi-separated scheme, intersections of two quasi-compact opens are
   quasi-compact (use the quasi-compact diagonal);
2. hence a quasi-compact open is retrocompact;
3. because `X` is quasi-compact, a retrocompact open is quasi-compact by
   intersecting it with `X`;
4. a quasi-compact open has a finite affine subcover;
5. a finite union of affine opens is quasi-compact.

### 2.3 Proof of `(2) -> (4)`

Let `T = X \ U`.  Construct the reduced closed complement ideal `J`:

```text
J(V) = {f in O_X(V) | f maps to 0 in k(t) for every t in T ∩ V}.
```

On `Spec R`, this is the radical ideal cutting out `T ∩ Spec R`.  Prove:

1. these affine ideals localize correctly and form a quasi-coherent ideal;
2. `V(J) = T`;
3. `J|_U = O_U`.

Apply 01PF to the finite-type submodule

```text
O_U = J|_U ≤ J|_U
```

inside the quasi-coherent ambient module `J`.  Obtain a finite-type
quasi-coherent `I ≤ J` with `I|_U = O_U`.  Then:

- `I ≤ J` implies `V(J) ⊆ V(I)`, hence `T ⊆ V(I)`;
- `I|_U = O_U` implies `V(I) ∩ U = ∅`, hence `V(I) ⊆ T`;
- consequently `V(I) = T`.

The equality is set-theoretic; do not assert equality of closed subschemes.

### 2.4 Proof of `(4) -> (1)`

Let `W = Spec R` be affine.  Restrict `I` to `W`, obtaining `I~` for a
finitely generated ideal `I ≤ R`.  Then

```text
U ∩ W = Spec R \ V(I) = D(I),
```

a finite union of standard opens and therefore quasi-compact.  The affine
test for retrocompactness gives that `U` is retrocompact.

Extract:

1. `Ideal.FG.isCompact_compl_zeroLocus`;
2. `retrocompact_iff_inter_affine_compact`;
3. `isRetrocompact_of_finiteType_complementIdeal`.

### 2.5 Constructible-closed corollary

If `T ⊂ U` is closed and constructible and `U` is qcqs, then `U \ T` is
open constructible, hence quasi-compact in the spectral space `U`.  Apply
01PH to get a finite-type ideal `J_T` on `U` with `V(J_T)=T`.  This is the
precise input to 0F3V(2).

## 3. Tag 080L: admissible blow-ups compose

### 3.1 Exact statement and typing correction

Let `X` be qcqs and `U : X.Opens` quasi-compact.  If `b : X' ⟶ X` is
`U`-admissible and `c : X'' ⟶ X'` is admissible with respect to the pulled
back open `b ⁻¹ᵁ U`, then `c ≫ b` is `U`-admissible.

Stacks writes the second hypothesis as “a `U`-admissible blowup” by
identifying `b⁻¹(U)` with `U`.  Lean must not make this abuse of notation.

The printed proof is one line: apply the stronger composition theorem
[080B](https://stacks.math.columbia.edu/tag/080B).  Therefore 080B is the
real formalization task.

### 3.2 Short proof once 080B exists

Unpack the two admissibility witnesses:

- `Z ⊂ X`, finite presentation, `Z ∩ U = ∅`, and `X' ≅ Bl_Z X`;
- `Z' ⊂ X'`, finite presentation,
  `Z' ∩ b⁻¹(U) = ∅`, and `X'' ≅ Bl_Z' X'`.

080B supplies a finite-presentation center `Y ⊂ X` with

```text
|Y| = |Z| ∪ b(|Z'|)
```

and an isomorphism over `X`

```text
X'' ≅ Bl_Y X.
```

Prove the separate topological lemma

```text
Disjoint |Z'| (b ⁻¹' U) -> Disjoint (b '' |Z'|) U.
```

Both terms in the support union miss `U`, so `Y` is an admissible center.
If chosen open isomorphisms are bundled, define the result using pullback
associativity followed by the composite of the two open isomorphisms.

### 3.3 Formalization of 080B

Let `I` cut out `Z`, let `A = ⊕ I^n`, and identify `X'` with
`Proj_X(A)`.

#### A. Encode the second center in finite degree

Set

```text
U0 = X \ (|Z| ∪ b(|Z'|)).
```

Prove `U0` is quasi-compact.  Apply the finite-degree relative-Proj result
[0803](https://stacks.math.columbia.edu/tag/0803): obtain `d > 0` and a
finite-type submodule `F ≤ I^d` such that

```text
Z' = Proj_X(A / F A)
Supp(I^d / F) ⊆ X \ U0.
```

This theorem must be formalized faithfully.  Do not replace it with an
unproved “least positive degree” selection.

#### B. Construct the center downstairs

View `F ≤ I^d ≤ O_X` as a finite-type ideal `J`.  Prove:

1. `V(J) ⊆ X \ U0` using the support condition on `I^d/F` and the fact that
   `I^d = O_X` on `U0`;
2. `Z ⊆ V(J)` since `J ≤ I^d`;
3. over `X \ Z`, where the first blow-up is an isomorphism, `J` cuts out
   `Z'`;
4. therefore `V(J) = |Z| ∪ b(|Z'|)` set-theoretically.

Put `K = I J`.  It is finite type and

```text
V(K) = V(I) ∪ V(J) = |Z| ∪ b(|Z'|).
```

Let `Y = V(K)`.

#### C. Identify the iterated blow-up

Use the product-ideal blow-up theorem
[080A](https://stacks.math.columbia.edu/tag/080A) to compare

```text
Bl_K X  ≅  Bl_(b⁻¹J O_X') X'.
```

On a standard chart `A[I/a]`, if `M ≤ I^d` represents `F`, the ideal of
`Z'` is generated by `m/a^d`.  If `m` corresponds to `f ∈ J`, then

```text
f = a^d (m/a^d).
```

Thus, on `X'`,

```text
b⁻¹J O_X' = I_E^d I_Z',
```

where `I_E=(a)` is the exceptional Cartier ideal.  Prove equality on each
standard chart and glue by ideal-sheaf extensionality.  The Stacks page says
this equality is “on `X''`”; its terms are ideals on `X'`, which is the
type-correct formulation.

Since `I_E^d` is invertible, blowing up `I_E^d I_Z'` agrees with blowing up
`I_Z'`: use “blowing up a Cartier ideal is the identity”
([0807](https://stacks.math.columbia.edu/tag/0807)) and 080A, or prove it
directly from the universal property [0806](https://stacks.math.columbia.edu/tag/0806).
Compose the over-`X` isomorphisms to finish 080B.

### 3.4 Extracted declarations

1. `finiteDegreeIdealOfClosedInRelativeProj` (0803);
2. `compositionCenterIdeal` and its finite-type/support theorem;
3. `extend_compositionCenterIdeal_eq_exceptional_mul_center`;
4. `blowup_mul_invertible_iso`;
5. `compIsoBlowup` (080B), as an iso in `Over X`;
6. `image_disjoint_of_preimage_disjoint`;
7. `AdmissibleBlowup.comp` (080L).

## 4. Tag 0F3V: separating closed/constructible boundary pieces

### 4.1 Exact statement

Let `X` be qcqs and `U ⊂ X` quasi-compact open.

1. If `Z₁,Z₂ ⊂ X` are closed subschemes of finite presentation and
   `Z₁ ∩ Z₂ ∩ U = ∅`, some `U`-admissible blow-up has disjoint strict
   transforms of `Z₁` and `Z₂`.
2. If `T₁,T₂ ⊂ U` are disjoint constructible subsets closed in `U`, some
   `U`-admissible blow-up has disjoint closures of `T₁` and `T₂`.

These should be two public theorems.  The second depends on the first.

### 4.2 Part (1): closed subschemes

Let `I_i` be the finite-type ideals of `Z_i` and define

```text
Z = V(I₁ I₂).
```

#### A. Product center over U

The empty triple intersection gives

```text
(I₁ + I₂)|_U = O_U.
```

Use the Chinese remainder theorem to prove a scheme isomorphism

```text
Z ×_X U ≅ (Z₁ ×_X U) ⨿ (Z₂ ×_X U).
```

Denote the two summands by `P₁,P₂`.  Prove that they are disjoint
quasi-compact opens of `Z`.

#### B. Strong separation of two qc opens (080P)

The Stacks proof invokes [080P](https://stacks.math.columbia.edu/tag/080P).
Formalize the stronger construction, not only its existential conclusion.

For disjoint qc opens `P₁,P₂ ⊂ Z`:

1. use 01PH to choose finite-type ideals `A_i` with
   `V(A_i)=Z\P_i`;
2. `V(A₁A₂)=Z`, so `A₁A₂` is locally nilpotent;
3. finite generation on affine charts plus a finite affine cover of `Z`
   gives a uniform `n>0` with `A₁^n A₂^n=0`;
4. put `K=A₁^n+A₂^n`; then
   `V(K)=Z\(P₁∪P₂)`;
5. blow up `K`.

On a chart indexed by `a∈A₁^n`, multiplication by `a` is injective in the
blow-up algebra, while `a A₂^n=0`; hence the extended `A₂^n` is zero.
Symmetrically the extended `A₁^n` is zero on `A₂^n`-charts.  A mixed chart is
empty because its product denominator is both regular and zero.

The Stacks proof omits the global gluing.  Formalization must prove:

- each chart family is open;
- the two unions cover the blow-up;
- the unions are disjoint;
- because they are complementary opens, each is also closed;
- the construction is independent of the chosen affine chart and generators;
- `P_i` pulls back into the corresponding component.

Package the result with its explicit center and clopen decomposition.

#### C. Move the center from Z to X

Let `Y=V(K) ⊂ Z`.  The ideals and 01TV show `Y ⟶ Z` and `Z ⟶ X` are
closed immersions of finite presentation; 01TR gives this for `Y ⟶ X`.
The support formula gives `Y ∩ U=∅`.  Blow up `X` in this composite center.

Use strict-transform compatibility
[080E](https://stacks.math.columbia.edu/tag/080E):

```text
strictTransform_X(Z) ≅ Bl_Y Z.
```

Then prove a transitivity/ambient lemma saying that the strict transform of
`Z_i` computed in `Bl_Y X` agrees with the one computed inside `Bl_Y Z`.
The latter lies in the appropriate clopen component, so the two strict
transforms are disjoint.

### 4.3 Part (2): constructible closed subsets

For each `i`:

1. set `W_i = U \ T_i`;
2. prove `W_i` is open constructible and hence quasi-compact;
3. by 01PH choose a finite-type ideal `J_i ≤ O_U` with `V(J_i)=T_i`;
4. by the ideal specialization of 01PF extend it to a finite-type ideal
   `I_i ≤ O_X` with `I_i|_U ≅ J_i`;
5. set `Z_i=V(I_i)` and prove `|Z_i×_XU|=T_i`;
6. disjointness of `T₁,T₂` gives the hypothesis of part (1).

Let `B : X' ⟶ X` be the result of part (1).  Over `U`, use the chosen or
canonical isomorphism `B⁻¹(U)≅U` to regard `T_i` as subsets of `X'`.  Prove:

```text
closure_X' (image T_i) ⊆ |strictTransform_B Z_i|.
```

This follows because the strict transform is a closed subscheme and its
restriction over `U` contains exactly `T_i`.  The two strict-transform
supports are disjoint, so the two closures are disjoint.

### 4.4 Extracted declarations

1. `productCenter_restrict_disjointUnion` (CRT);
2. `finiteTypeIdeal_uniformlyNilpotent_of_support_univ`;
3. `zeroProduct_chartSeparation`;
4. `separateQcOpensBlowup` with explicit center and clopen components (080P);
5. `strictTransform_of_factor_through_closed` / ambient compatibility;
6. `exists_admissibleBlowup_disjoint_strictTransforms` (0F3V(1));
7. `constructibleClosedSupportIdeal` (01PH corollary);
8. `closure_image_le_strictTransform_support`;
9. `exists_admissibleBlowup_disjoint_closures` (0F3V(2)).

## 5. Implementation order and milestones

### Phase A: sheaves and opens

1. Define finite type for ideal-sheaf data and restriction.
2. Prove the affine localization/finite-generation lemmas.
3. Prove quasi-coherent submodule extension (01PE).
4. Prove binary gluing and finite affine induction.
5. Finish 01PF.
6. Construct the reduced complement ideal and finish all implications of
   01PH.

Acceptance criterion: both 01PF and the four-way 01PH equivalence compile
without any blow-up definitions.

### Phase B: blow-up foundation

1. Rees algebra and affine `Proj` charts.
2. Global/relative blow-up by gluing affine charts.
3. complement-of-center isomorphism and universal property;
4. exceptional Cartier ideal;
5. product-ideal comparison and removal of an invertible factor;
6. strict transforms, chart formula, and ambient compatibility.

Acceptance criterion: 080A, 080E, and the universal property are available
as reusable theorems.

### Phase C: composition

1. Formalize 0803 (finite-degree description of a closed subscheme of a
   relative Proj);
2. construct the 080B center and prove its support formula;
3. prove the chartwise exceptional-factor equality and globalize it;
4. prove 080B in `Over X`;
5. derive 080L and, if bundled, its open-isomorphism coherence.

Acceptance criterion: the composite morphism, not merely its source scheme,
is identified with the new blow-up over `X`.

### Phase D: separation

1. Prove uniform nilpotence and the zero-product chart lemma;
2. finish the omitted gluing in 080P;
3. prove CRT decomposition of the product center;
4. prove 0F3V(1) using ambient strict-transform compatibility;
5. prove the constructible corollary of 01PH, extend its ideals by 01PF, and
   prove 0F3V(2).

Acceptance criterion: disjointness is a theorem about closed subschemes (or
their supports after an explicit conversion), and the closure statement
transports subsets through the open isomorphism explicitly.

## 6. Audit of the existing workspace blueprint

The relevant material is already present in
`weil_conjectures_proof_blueprint.tex`, but the following changes are needed
before treating it as a dependency-complete formalization plan.

### 6.1 Tag 01PF

- The general result is the block
  `lemma:nagata-qcqs-finite-type-submodule-extension` near lines 5513–5550.
  This is the actual content of 01PF and should carry the 01PF citation.
- The cited blocks near lines 5569–5588 and 5800–5816 are ideal
  specializations/packaging corollaries, not the full Stacks lemma.
- The `\uses` list for the general result should name the arbitrary
  quasi-coherent extension theorem (01PE), affine finite-generation lemma,
  quasi-compactness of overlaps, binary subobject gluing, and locality of
  finite type/quasi-coherence.

### 6.2 Tag 01PH

- The blocks near lines 5923–5958 and 7654–7669 use only `(2)->(4)` and its
  constructible-closed corollary.  They do not formalize the four-way
  equivalence in 01PH.
- If only the forward direction is needed locally, rename it accordingly and
  state that it is the required implication of 01PH; otherwise add the
  reverse retrocompactness proof.
- The constructible-support proof must explicitly depend on the theorem that
  open constructible subsets of spectral spaces are quasi-compact.

### 6.3 Tag 080L

- The block near lines 5311–5332 correctly routes through the expanded 080B
  theorem, but “the second center is disjoint from its inverse image” is
  ambiguous and ill-typed.  Replace it by the explicit image/preimage
  disjointness lemma.
- Its statement uses a stronger bundled admissibility notion than Stacks.
  Record the pullback associator and composite open isomorphism as separate
  coherence data.
- In the 080B development near lines 3995–4176, the finite-degree selection
  corresponding to 0803 is not proved.  The existing “least positive
  multiple” language should be replaced by a theorem with an existence proof;
  minimality is unnecessary.
- The support argument and chartwise-to-global ideal equality each need their
  own extracted lemmas.

### 6.4 Tag 0F3V

- The block near lines 7578–7620 implements part (1); the constructible blocks
  near lines 7642–7708 implement part (2).  This is a sound high-level split.
- The explicit construction is stronger than the short Stacks proof and is
  useful, but it must prove the omitted chart-family gluing from 080P.
- The step asserting what each strict transform is the closure of needs a
  scheme-theoretic closure/strict-transform comparison, not only a statement
  about underlying topological closures.
- Moving `Y⊂Z` to a center in `X` and comparing strict transforms requires an
  explicit composite-closed-immersion ideal and canonical isomorphisms; these
  are not definitional equalities.

## 7. Principal risks

1. **Infrastructure gap.** Current Mathlib has useful ideal-sheaf data and
   absolute graded-ring `Proj` foundations, but the global relative blow-up,
   strict-transform, and admissible-blow-up API used here is project-level
   work.
2. **Subobject equality.** Many paper equalities are canonical isomorphisms in
   Lean; trying to force definitional equality will make gluing brittle.
3. **Open typing.** The second open in 080L lives on `X'`, and subsets in
   0F3V(2) must be transported through an open isomorphism.
4. **Set versus scheme.** 01PH gives a set-theoretic zero locus; 0F3V starts
   with closed subschemes; strict transforms are scheme-theoretic.  Conversion
   lemmas must be visible.
5. **Omitted proofs.** The largest hidden obligations are 0803 and the global
   gluing in 080P, not the final one-line arguments of 080L or 0F3V.

