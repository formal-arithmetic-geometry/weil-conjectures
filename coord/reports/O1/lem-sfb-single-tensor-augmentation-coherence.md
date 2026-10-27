## Worker report

The module `Sheaf.AlgebraicGeometry.SingleTensorAugmentationCoherence` states the node
without changing its mathematical statement or dependency lists. Its two declarations are
`AlgebraicGeometry.SchemeSingleTensorAugmentationCoherence` (a fully defined proposition
bundling this precise assertion) and
`AlgebraicGeometry.scheme_single_tensor_augmentation_coherence` (the assertion, with `sorry`).
The predicate is a packaging helper of this node, not another tensor or monoidal construction.
Its body has real data throughout. Its instance bindings and abbreviations are inside the
definition, not local declarations affecting the exported theorem signature. The theorem
has no `let` binders. No other theorem is introduced or proved.

Hypothesis and clause correspondence:

- Any scheme: `(X : Scheme.{u})`; there are no geometric assumptions. The independent
  `[HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]` selects the
  already recorded localization in any chosen derived-category morphism universe.
- All O_X-module sheaves: `SheafOfModules.{u} (moduleRings X.toRingedSpace)`, the shared
  carrier underlying `ringedSiteModules` and `schemeDerivedCategory`, not the separately
  bundled category instance on `X.Modules`. The binders `F G` range over every such sheaf;
  the associativity field also ranges over every third sheaf.
- Ordinary tensor and its symmetric constraints: the predicate binds exactly
  `SheafOfModules.monoidalCategory X.sheaf` and `SheafOfModules.symmetricCategory X.sheaf`.
  The additive and closed structures come from `SheafOfModules.tensorClosed X.sheaf`.
- Derived tensor: the instance is explicitly `schemeDerivedTensorMonoidal X`.
  `RingedDerivedNative.derivedSymmetric` supplies its descended Koszul braiding; it does
  not replace the derived tensor by a separately chosen monoidal structure.
- Degree-zero embedding: `t = CochainComplex.singleFunctor ... 0` and
  `s = DerivedCategory.singleFunctor ... 0`. Mathlib's `singleFunctorIsoCompQ` is `Iso.refl`,
  so `s` is definitionally the composite `t ⋙ Q`.
- Canonical morphism: the local term `m F G` is the actual composite
  `Functor.LaxMonoidal.μ Q (t.obj F) (t.obj G) ≫
  Q.map (DerivedCategory.moduleCup_singleTensorIso F G).hom`.
  Its source is `sF ⊗ᴸ sG` and target is `s(F ⊗ G)`. The equality
  `h.toLaxMonoidal.μ F G = m F G` fixes every component; the existential structure cannot
  substitute arbitrary maps with the same endpoints.
- Naturality: the `μ_natural_left` and `μ_natural_right` fields of the existential
  `h : s.LaxBraided` give naturality in each variable, hence simultaneous naturality.
- Associativity: `h.toLaxMonoidal.associativity` says
  `m F G ▷ sL ≫ m (F ⊗ G) L ≫ s.map (α_ F G L).hom =
  (α_ sF sG sL).hom ≫ sF ◁ m G L ≫ m F (G ⊗ L)`.
  This is exactly the displayed diagram in categorical composition order.
- Symmetry: `h.braided` says
  `m F G ≫ s.map (β_ F G).hom = (β_ sF sG).hom ≫ m G F`, exactly the
  displayed symmetry equation. Source and target categories carry the symmetric
  structures just specified, so lax braided here means lax symmetric monoidal.
- Normalized degree-zero unit: `h.toLaxMonoidal.ε = Functor.LaxMonoidal.ε Q`, together
  with `IsIso (Functor.LaxMonoidal.ε Q)`. The complex unit is O_X[0], and this fixed
  native comparison is the canonical identification of the derived unit with
  `s O_X`. Under that identification the unit morphism is the identity. No arbitrary
  isomorphism or scalar is chosen. This is how the node's normalized equality is
  represented when the localization's units are not literally the same Lean object.
- Left and right unit equations: `h.toLaxMonoidal.left_unitality` and
  `h.toLaxMonoidal.right_unitality` give precisely the two displayed equations after
  this fixed unit identification. The unit comparison factors required for the
  endpoints by Mathlib are identities under that normalization.
- Every permitted pair of resolutions: the final clause universally quantifies over
  `P T` and augmentations `a : P ⟶ t.obj F`, `b : T ⟶ t.obj G`.
  `P.IsStrictlyLE 0`, `T.IsStrictlyLE 0` mean nonpositive; `QuasiIso a`, `QuasiIso b`
  mean resolution; `∀ i, ObjectProperty.flat (P.X i)` and its T analogue mean termwise
  flatness; `IsKFlatIndependentCoefficients (R := X.sheaf)` is the recorded acyclic-tensor
  K-flatness, with exactly the ordinary sheaf tensor. No degreewise epimorphism is added.
- Representative normalization: `IsIso (μ Q P T)` asserts that the fixed source model
  comparison is invertible. The equation
  `(Q.map a ⊗ₘ Q.map b) ≫ m F G =
  μ Q P T ≫ Q.map ((a ⊗ₘ b) ≫ (moduleCup_singleTensorIso F G).hom)`
  identifies the representative after this invertible comparison with the tensor of
  both augmentations followed by the existing unsigned total/single isomorphism.
  Equivalently, precompose the equation with `(asIso (μ Q P T)).inv` to obtain the
  node's map out of `Q(Tot(P ⊗ T))`. This is not merely an unnormalized existence
  assertion, nor a formula for one selected resolution.
- No flatness, quasi-coherence or finiteness of F, G or L: none occurs. No assertion
  `IsIso (m F G)` occurs; only the K-flat source-model and unit comparisons are invertible.

Dependency declarations used (their complete signatures and docstrings were read):

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme` and `.Scheme.Hom`.
- `Sheaf.CategoryTheory.RingedSiteModules`: `CategoryTheory.ringedSiteModules`, the
  transparent abbreviation of Mathlib's `SheafOfModules` used on the shared carrier.
- `WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorClosed`:
  `SheafOfModules.tensorClosed`, and its recorded monoidal/symmetric structures.
- `WeilConjectures.AlgebraicGeometry.DerivedTensorStructure`:
  `AlgebraicGeometry.schemeDerivedTensorMonoidal` and
  `AlgebraicGeometry.schemeModule_hasFunctorialFlatResolution`.
- `Sheaf.Algebra.Homology.KFlatIndependentCoefficients`:
  `CochainComplex.IsKFlatIndependentCoefficients`.
- `Sheaf.Algebra.Category.ModuleCat.Sheaf.FlatOnSite` exposes
  `CategoryTheory.ObjectProperty.flat`, the exact tensor-functor predicate.
- `Mathlib.Algebra.Homology.BifunctorShift`: `CochainComplex.mapBifunctor` and the native
  complex tensor implementing that signed direct-sum total tensor; no second totalization.
- `Sheaf.Algebra.Homology.RingedDerivedTensorNative`:
  `CategoryTheory.RingedDerivedNative.derivedSymmetric` and, for the proof plan,
  `localization_isIso_mu`, `kFlat_of_acyclic`, `localizationLaxBraided` and `isIso_ε`.
- `Sheaf.Algebra.Homology.RingedTensorComplexConstraints`: `complexConstraints`, whose
  pure-generator formulas are used in the proof plan for the single-complex constraints.
- `Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients`:
  `CochainComplex.exists_isKFlatResolutionIndependentCoefficients`, for the proof plan.
- `Mathlib.CategoryTheory.Sites.Sheafification` and `.LocallyBijective`: the finite-limit
  preservation instance for `presheafToSheaf`, `W_iff_isLocallyBijective` and `W_iff`,
  for the proof plan. These are the recorded Mathlib matches, despite absent Lean records.
- Existing helper `DerivedCategory.moduleCup_singleTensorIso` from
  `WeilConjectures.AlgebraicGeometry.ModuleCupCanonicalHZeroIdentification` supplies the
  unsigned identification already used upstream. This helper, not the H-zero theorem,
  is used; it is not redefined.

Edge cases checked mathematically against the written signature: the empty scheme and
zero sheaves are allowed; zero complexes and all zero augmentations that are quasi-isomorphisms
are allowed. The ring unit is included. Sheaves with nonzero Tor are allowed, so the map is
not required invertible. In degree (0,0) the Koszul sign is 1, including in characteristic 2;
no sign hypothesis or characteristic restriction occurs. Resolutions are nonpositive rather
than nonnegative, have no extra surjectivity assumption, and both are universally quantified.
The intermediate tensor F ⊗ G need not be flat. The universes u and w remain independent.
The small Zariski site has opens and morphisms in u, so the coefficient universe u is valid.

Searches (2026-10-24):

- `msearch.py ... leanfinder "The degree zero embedding of module sheaves into the derived
  category is lax symmetric monoidal with tensor of flat resolution augmentations"`:
  eight hits, including Tor, Tor', a condensed sheafification monoidal instance and
  HomologicalComplex.Monoidal.inducingFunctorData. None states this assertion.
- `msearch.py ... loogle "singleFunctor, Monoidal"`: zero hits (unknown identifier
  singleFunctor in the search parser); followed by direct Mathlib source inspection.
- `msearch.py ... grep "single.*[Ll]ax|[Ll]ax.*single|single.*[Mm]onoidal" CategoryTheory`:
  seven hits about bicategorical single objects, action categories and cartesian
  monoidal functors; none is the required statement.
- `msearch.py ... leansearch "The single complex functor is lax symmetric monoidal for
  derived tensor with canonical augmentation comparison"`: eight hits, including
  Functor.LaxMonoidal, Functor.LaxBraided.toLaxMonoidal and ofTensorHom. These are the
  generic coherence structures used here, not a theorem asserting our canonical maps.
- `rg` in both `lean/WeilConjectures` and `lean/Sheaf` for single/monoidal/lax, Q tensor
  comparison and single tensor names found `moduleCup_singleTensorIso` and the canonical
  H-zero comparison. The former is reused. The latter asserts invertibility on H-zero
  and a one-sided resolution transport, not all the present coherence laws.
- `grep -rn "lem-sfb-single-tensor-augmentation-coherence" lean/WeilConjectures` found
  no already attached declaration. `rg` in the upstream-name index and both source roots
  for our two full declaration names found no collision.

Sources: the live `literature/stacks-project/cohomology.tex`, at
`definition-derived-tor` and `lemma-symmetric-monoidal-derived`; the node itself explicitly
labels the augmentation coherence as an agent refinement rather than verbatim Stacks text.
No source-based correction, disputed statement, new node or dependency module was needed.

Validation: the delivered module compiled on the server via the prescribed `scompile.py`
against the live library, with no errors or warnings. Dry-run and delivery results follow
from the prescribed `deliver2.py` checks.

## Second reading by O1

Author's second pass, not an independent review: the dispatcher explicitly forbids starting
other agents, and the maintainer supplies the independent reading of this delivery.
I reread the node alongside the complete predicate body and the Mathlib LaxMonoidal and
LaxBraided fields. The tensorator and unit are fixed by equality, so the existential
structure does not lose their normalization. Associativity, both naturalities, symmetry
and both unit diagrams are exactly the bundled fields. The final clause uses both
augmentations, nonpositive degrees, flat terms and the recorded K-flat predicate, and
asserts the comparison invertible rather than requiring it as an extra hypothesis.
The ordinary and derived constraints are the recorded canonical ones. The node's
identification of units is represented by the canonical localization comparison, as
explained above, without a new choice. No missing clause or added geometric hypothesis
was found. No mathematical statement was changed during this pass.
