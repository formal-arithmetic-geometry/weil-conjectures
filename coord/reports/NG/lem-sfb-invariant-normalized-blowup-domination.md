## Worker report

The delivery states `AlgebraicGeometry.exists_invariant_normalized_blowup_domination` in
`Sheaf.AlgebraicGeometry.InvariantNormalizedBlowupDomination`. There is one named theorem,
with proof `sorry`; there are no definitions, new nodes, dependency repairs, or statement
changes. The repository was read only; all authored files are in this item's sandbox.

### Hypotheses and objects

- The field is `(k : Type u) [Field k]`. The specified finite-type projective integral
  k-scheme is `(S₀ : Scheme.{u}) (p : S₀ ⟶ Spec (.of k)) [IsIntegral S₀]
  [IsHProjective p] [LocallyOfFiniteType p] [QuasiCompact p]`. Finite type uses the
  recorded conjunction, and projective uses the finite-projective-space convention.
- Normality is `hnormal : ∀ x : S₀, IsDomain (S₀.presheaf.stalk x) ∧
  IsIntegrallyClosed (S₀.presheaf.stalk x)`, exactly the node's local-ring convention.
- The finite group is `(H : Type v) [Group H] [Fintype H]`. Fintype supplies the finite
  enumeration needed for the orbit product; every finite group admits it and the product
  is independent of the enumeration. Its universe v is independent of u. There is no
  injectivity hypothesis on either action.
- The two left actions are `σk : H →* (k ≃+* k)` and `σ₀ : H →* Aut S₀`.
  `hsemilinear` says `(σ₀ h).hom ≫ p = p ≫ Spec.map
  (CommRingCat.ofHom (σk h⁻¹).toRingHom)`. The inverse compensates for Spec's
  contravariance, following the landed EquivariantCurvePencil and
  EquivariantFlatCurvePreparation convention. It does not require k-linear actions.
- `I : S₀.IdealSheafData` is the existing quasi-coherent ideal-sheaf encoding;
  `hfinite : ∀ W : S₀.affineOpens, (I.ideal W).FG` is finite type on affine opens.
  The specified dense open is `U₀` with `hdense : Dense (U₀ : Set S₀)`.
  `hunit : I.comap U₀.ι = ⊤` says the ideal restricted to U₀ is the unit ideal.
- There is no new blowup or normalization construction. The theorem identifies the
  output open and ideal by `U = (⨅ h : H, (σ₀ h).inv ⁻¹ᵁ U₀)` and
  `J = (∏ h : H, I.comap (σ₀ h).inv)`. Inverse image under h inverse is the image
  h(U₀), and pullback along h inverse is the transported ideal h(I).
  `I.blowup` is V; `J.blowup` is B. Their maps are the existing `blowupMap`.

### Every conclusion

- B is integral through the existential instance `hB : IsIntegral J.blowup`.
  `IsProjectiveBundle J.blowupMap` is precisely its asserted projectivity convention.
- For every h, `∃! d : J.blowup ⟶ (I.comap (σ₀ h).inv).blowup,
  d ≫ (I.comap (σ₀ h).inv).blowupMap = J.blowupMap` gives canonical domination
  over S₀. Uniqueness expresses canonicality: these are maps to the actual translated
  blowups, with their actual projections. It also follows from density and separatedness.
- The normalization is expressed without choosing data from a sorry theorem:
  `S`, `ν : S ⟶ J.blowup`, and `e : S ≅ @Scheme.normalization J.blowup hB`, with
  `e.hom ≫ @Scheme.fromNormalization J.blowup hB = ν`. This is exactly the existing
  normalization in B's function field, up to its specified isomorphism over B.
- `IsFinite ν` gives finiteness. Its birationality is a dense open W of B, dense
  inverse image in S, and `IsIso (ν ∣_ W)`. This means an isomorphism of dense open
  subschemes, not a merely abstract equality of fields.
- S is integral by its existential `IsIntegral S` instance and normal by the displayed
  domain and integrally closed conditions on every stalk. Its structure map is the
  prescribed `ν ≫ J.blowupMap ≫ p`. `IsHProjective`, `LocallyOfFiniteType`, and
  `QuasiCompact` of that map say normal integral projective finite type over k.
- `IsHProjective (ν ≫ J.blowupMap)` gives H-projectivity of the modification, in the
  convention independent of the group. `IsIso ((ν ≫ J.blowupMap) ∣_ U)` and density
  of its inverse image, together with `Dense U`, give the specified isomorphism over U
  and birationality of S → S₀ in the dense-open sense.
- The function-field identification is the canonical stalk pullback: the theorem gives
  `hη : (ν ≫ J.blowupMap) (genericPoint S) = genericPoint S₀` and bijectivity of
  `S₀.presheaf.stalkSpecializes (specializes_of_eq hη) ≫
  (ν ≫ J.blowupMap).stalkMap (genericPoint S) : S₀.functionField ⟶ S.functionField`.
  Both rings are fields, so this is the claimed canonical field isomorphism, rather than
  an unrelated field equivalence. No algebra structure is postulated independently.
- `σB : H →* Aut J.blowup` and `σS : H →* Aut S` have the two equivariance squares
  `(σB h).hom ≫ J.blowupMap = J.blowupMap ≫ (σ₀ h).hom` and
  `(σS h).hom ≫ ν = ν ≫ (σB h).hom`. Together with hsemilinear these assert
  compatibility with the original action on k on both B and S as well. Monoid
  homomorphisms to Aut contain the group laws and inverse automorphisms.
- `∃ d : S ⟶ I.blowup, d ≫ I.blowupMap = ν ≫ J.blowupMap` is the stated
  S₀-morphism to V. The equality uses the prescribed projection, not an arbitrary map.
- `Dense (U : Set S₀)` and `(∀ h, (σ₀ h).hom '' (U : Set S₀) = U)` give density
  and invariance of exactly the finite intersection defined above.
- The closing text about schematic closure supplies a general convention but introduces
  no closure construction in this lemma; consequently it needs no spurious extra clause.

### Dependency declarations read and used

All thirteen statement dependency nodes were read, including their statements and recorded
Lean or Mathlib matches. Their source signatures and docstrings were read in the live read
clone, including the ideal-sheaf functoriality needed for transport.

- `def-weil-field`: `Field`, Mathlib.Algebra.Field.Defs (180).
- `def-pc-integral-scheme`: `AlgebraicGeometry.IsIntegral`,
  Mathlib.AlgebraicGeometry.Properties (240).
- `def-kun-projective`: `AlgebraicGeometry.IsHProjective`,
  WeilConjectures.AlgebraicGeometry.Morphisms.Projective (30–38). The module is
  imported publicly, including its projective-space definition and closed immersions.
- `def-weil-finite-type-morphism`: `AlgebraicGeometry.LocallyOfFiniteType` and
  `AlgebraicGeometry.QuasiCompact`, Mathlib.AlgebraicGeometry.Morphisms.FiniteType and
  QuasiCompact; finite type is their recorded conjunction.
- `pqf-def-coherent`: Sheaf.AlgebraicGeometry.CoherentFiniteType exposes
  `Scheme.Modules.IsQuasiCoherentFiniteType`, `SheafOfModules.IsQuasicoherent`,
  `SheafOfModules.IsFiniteType`, and `RingedSpace.IsCoherent`. The statement uses
  the affine finite-generation criterion for an IdealSheafData, as does the recorded
  IntegralBlowupProjectiveGeometry dependency; no alternate module notion is defined.
- `def-nagata-global-blowup`: `Scheme.IdealSheafData.blowup` and `blowupMap`,
  WeilConjectures.Blowup.Gluing (255, 260): gluing data's glued scheme and toBase.
- `def-sc-normalization`: `Scheme.normalization` and `Scheme.fromNormalization`,
  WeilConjectures.Mathlib.AlgebraicGeometry.Normalization (185, 190), with the integral
  instance explicitly supplied for the already specified B.
- `def-sc-function-field`: WeilConjectures.AlgebraicGeometry.FunctionField explicitly
  retains Mathlib `Scheme.functionField` for arbitrary integral schemes; the theorem
  uses this clause (the generic stalk), rather than its component-product extension.
- `def-weil-finite-integral-morphism`: `AlgebraicGeometry.IsFinite` and
  `AlgebraicGeometry.IsIntegralHom`, Mathlib.AlgebraicGeometry.Morphisms.Finite and
  Integral; the conclusion uses IsFinite.
- `def-trf-projective-bundle-morphism`: `AlgebraicGeometry.IsProjectiveBundle`,
  Sheaf.AlgebraicGeometry.ProjectiveBundleMorphism: finite-type quasi-coherent E and
  closed immersion into the relative Proj of its canonical graded symmetric algebra.
- `def-weil-closed-immersion`: `AlgebraicGeometry.IsClosedImmersion`,
  Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion, used by both projectivity notions.
- `def-sbc-closed-immersion-ideal-sheaf`: `Scheme.Hom.ker` and `Scheme.IdealSheafData`,
  Mathlib.AlgebraicGeometry.IdealSheaf.Basic; Mathlib's comap is defined using this ker.
- `def-sbc-ideal-sheaf-powers`: the same Basic module's semiring product, ideal_mul and
  ideal_pow; J uses that existing product. `Scheme.IdealSheafData.comap` from
  Mathlib.AlgebraicGeometry.IdealSheaf.Functorial is used for the automorphism transport.

All recorded proof-dependency modules are imported non-publicly unless already imported
publicly for the statement. This includes IntegralBlowupProjectiveGeometry,
ProjectiveBundleProper, the finite-type and quasi-compactness composition/base-change
modules, Blowup.Complement, Blowup.Principalization, Blowup.BlowupUniversal,
ProjectiveAmpleInvertible, ProjectiveBundleToHProjective, HProjectiveComposition,
and Morphisms.FiniteProjectiveBundle. Normalization existence and normal-locus assertions
are in the normalization module already imported publicly. The proof dependency
`lem-sfb-finite-normalization-model-functoriality` currently has neither a Lean record nor
Mathlib match, so there is no recorded module to import; it supplies no object required to
TYPE this statement, whose normalization construction already exists. Its proof is not
assumed as an extra hypothesis. The theorem docstring carries all eight DAG proof steps
and their dependency ids for stage 3.

### Sources and edge cases

Read Stacks divisors.tex, lemma-blow-up-integral-scheme (02ND),
lemma-blowing-up-projective (02NS), and the source's universal-property discussion;
morphisms.tex, lemma-nagata-normalization (035S) and
lemma-projective-over-quasi-projective-is-H-projective (087S). The affine blowup charts
and product-factor universal property agree with the eight-step synthesis in the node.
The field is arbitrary: finite-type schemes over a field are Nagata, so the finite
normalization conclusion needs no extra assumption on k. Normality of S₀ ensures that
normalization remains an isomorphism over the specified U.

Checked: H trivial gives the ordinary normalization of Bl_I; arbitrary nonfaithful actions
are retained; the action on k may be nontrivial; I = O gives unit ideal product and an
isomorphism over the whole base when U₀ is the whole base; nonzero invertible I also has
identity blowup, with the uniquely determined comparisons. A zero ideal is impossible on
a nonempty dense open of the integral base, so no hI ≠ 0 was added. Empty S₀ and empty U₀
are excluded by the actual integral and dense hypotheses, not by an extra condition.
For a zero-dimensional base Spec K the only permitted I is the unit ideal; all assertions
reduce to the normal field scheme and its given action. The group has an identity, so the
orbit is never empty; the auxiliary product with one factor omitted in proof step 4 may
be empty and then equals the unit ideal. Universes u and v remain independent; no action
is required faithful or k-linear. No STATEMENT-DISPUTED fault was found.

### Searches performed

Prescribed msearch.py calls, recorded by the wrapper:

- leanfinder: "A finite semilinear group action lifts to the normalization of the blowup
  of the product of translated ideals, dominating every translated blowup." Eight hits
  about relative normalization diagrams, normalizationDesc, and their maps; none states
  the orbit product, the actions, or the domination theorem.
- loogle: "AlgebraicGeometry.Scheme.normalization,
  AlgebraicGeometry.Scheme.IdealSheafData.blowup". Zero hits; the remote service reports
  unknown identifier Scheme.normalization, which is an upstream extension. This is not
  treated as evidence that the locally read normalization construction is absent.
- grep Mathlib: "normalized.*blowup|blowup.*normaliz|invariant.*blowup". Zero hits.
- leansearch: "Normalization of the blowup of the product of translated ideals carries
  a finite semilinear group action and dominates each translated blowup." Eight hits:
  relative normalization maps/instances, a Galois prime-orbit lemma, and normalize_apply;
  none gives this theorem.

Direct rg searches of lean/WeilConjectures and lean/Sheaf for the item id,
"invariant.*blowup", "normalized.*blowup", and "orbit.*ideal" found existing general
normalized blowup calculus and log blowup comparisons, but no statement of this orbit
construction. The exact new declaration name was also searched in those trees and in
 dag/lean_names_upstream.json; it is unused. Read the existing NormalizedBlowup module:
its construction is the componentwise reduced normalization, whereas the present lemma
uses the already existing integral function-field normalization after asserting B integral;
no second normalized-blowup definition is introduced. No new notion needed a new node.

### Validation

The prescribed scompile.py compiled the theorem against the published server library in
both its sandbox and named module checks, with no errors or warnings. The final delivery
is also checked by deliver2.py's server compile and maintainer preflight. Only the expected
stage-2 theorem proof is postponed. No local or global library build was run.

## Second reading by NG

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
