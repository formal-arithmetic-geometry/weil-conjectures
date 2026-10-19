## Worker report

Record the existing `AlgebraicGeometry.Etale.derivedTensor` from
`WeilConjectures.SixFunctors.Etale.Derived.Tensor` (slopmaster2). No new module,
construction, theorem, hypothesis, or statement correction is needed. The node copy
changes only `lean`; its signature is copied verbatim from the source, including the
source's variable names `A` and `X`. Its parameters are supplied by the preceding
explicit `variable` declarations, which were read along with its docstring and body.

The source is the blueprint file named in the node, especially the displayed
K-flat-model formula. The expanded DAG statement also specifies ordinary totalization,
cohomology, quasi-isomorphisms, and the relation to the ringed-site K-flat predicate.
The source module explicitly constructs the unbounded derived tensor by the K-flat
left derivability structure, rather than choosing an unspecified bifunctor.

Hypotheses and clauses, individually:

- A commutative ring Λ: specialize the coefficient category `A` to
  `ModuleCat.{u + 1} Λ` with `Λ : Type (u + 1)` and `[CommRing Λ]`.
  All the generic coefficient-category assumptions on the upstream declaration
  (abelian, Grothendieck, symmetric monoidal, additive tensor, closed tensor, and
  functorial flat resolutions) are instances in this specialization. They are not
  extra hypotheses on Λ or T; the specialization was compiled with only these binders.
- An arbitrary scheme T: `T : Scheme.{u}`. There is no separatedness, Noetherian,
  nonemptiness, characteristic, coefficient torsion, or finiteness assumption.
- The small etale site: `T.smallEtaleTopology` on `T.Etale`, exactly the declaration
  of `def-weil-pbc-etale-site`, not a big or pro-etale site.
- The constant ring and its module sheaves: the existing coefficient encoding is
  `Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} Λ)`. A sheaf valued in Λ-modules
  is a sheaf of modules over the constant ring sheaf Λ_T: the constant-presheaf
  action factors uniquely through sheafification. This is the very encoding
  explicitly required by the recorded `def-weil-pbc-derived-categories` interface.
  There is no replacement by sheaves of sets or by modules of global sections.
- The unbounded derived category: specializing the source signature gives
  `Etale.DerivedCategoryModule Λ T ⥤ Etale.DerivedCategoryModule Λ T ⥤
  Etale.DerivedCategoryModule Λ T`. A typed `#check` confirmed this identification.
  `DerivedCategory.Q` is localization of cochain complexes at quasi-isomorphisms;
  the intermediate homotopy-category localization is related by
  `DerivedCategory.quotientCompQhIso`.
- Complexes have all integer cochain degrees: `CochainComplex _ ℤ`, i.e.
  `HomologicalComplex _ (ComplexShape.up ℤ)`. The Mathlib definition and docstring
  specify differential relation `i + 1 = j` and square-zero differentials.
- Acyclicity is the existing `HomologicalComplex.Acyclic`; its definition is exactness
  at every integer, equivalent to `IsZero (K.homology i)` by
  `HomologicalComplex.exactAt_iff_isZero_homology`.
- Quasi-isomorphisms are the existing `QuasiIso`, whose fields impose `QuasiIsoAt`
  at every integer, equivalent to isomorphism on every homology object. No bounded
  quasi-isomorphism test is substituted.
- Ordinary tensor is the direct-sum total tensor complex:
  `HomologicalComplex.tensorObj` in `Mathlib.Algebra.Homology.Monoidal` is explicitly
  `mapBifunctor K₁ K₂ (curriedTensor C) c`. For `c = ComplexShape.up ℤ` this is the
  `CochainComplex.mapBifunctor` recorded by `def-pc-tensor-complex-sheaves`.
  The graded tensor is a coproduct over `p + q = n`; it is not product totalization.
  The `ComplexShapeSigns` instance has first sign 1 and second sign `p.negOnePow`,
  so the differential is precisely `d_E tensor 1 + (-1)^p 1 tensor d_F`.
- K-flatness: the node's `CochainComplex.IsKFlat` tests acyclic complexes on the
  left, while its prose first puts the acyclic complex on the right. The signed
  symmetry has sign `(p * q).negOnePow` (`ComplexShapeSigns`), identifying these
  tests. The upstream localization machinery uses `MorphismProperty.kFlat`,
  which says tensoring on either side preserves quasi-isomorphisms. These are the
  same mathematical condition here: a map is a quasi-isomorphism exactly when
  its cone is acyclic, and additive total tensor commutes with cones; conversely
  test the quasi-isomorphism from zero into any acyclic complex. Thus no stronger
  requirement such as flatness of each term or boundedness is imposed on P.
- Choose representatives C₁, C₂ and a K-flat quasi-isomorphism `P ⟶ C₁`:
  the generic resolution theorem in the dependencies supplies such P; its extra
  flat-term and epimorphism properties are not assumptions on the objects of
  the derived tensor. The upstream `DerivedCategory.exists_kFlat_iso` likewise
  supplies K-flat representatives inside its localization construction.
- The formula `K₁ tensor^L K₂ = Q(P tensor C₂)`: the upstream
  `DerivedCategory.tensorLeftCounit` has components
  `Qh(P) tensor^L Qh(C₂) ⟶ Qh(P tensor C₂)`, and
  `DerivedCategory.isIso_tensorLeftCounit` makes these isomorphisms when P is
  K-flat. Use `quotientCompQhIso` to pass from Qh to Q, and invert `Q.map f` for
  the quasi-isomorphism `f : P ⟶ C₁`. This gives exactly the representative
  formula in the node. Equality of representatives means this isomorphism in
  the localization; it does not demand equality of distinct chosen complexes.
- Independence: the existing bifunctor is the K-flat total left derived tensor
  (the source's `isLeftDerivedFunctor₂_derivedTensor`). This node introduces no
  additional independence theorem; its downstream properties remain separate.
- Integer coefficients and the termwise constant complex: use the same declaration
  with `ModuleCat.{u + 1} (ULift.{u + 1} ℤ)`. Restriction along
  `(ULift.ringEquiv (R := ℤ)).symm.toRingHom`, followed by
  `forget₂ (ModuleCat.{u + 1} ℤ) AddCommGrpCat.{u + 1}`, identifies these coefficients
  with abelian groups. Both factors are equivalences (restriction along a ring
  isomorphism; unique integer-module structure). Sheaf and derived equivalences
  give the usual integer-coefficient notation. The complex in the right slot is
  `(constantSheaf T.smallEtaleTopology (ModuleCat Λ)).mapHomologicalComplex
  (ComplexShape.up ℤ)`, the exact existing declaration of `def-kun-constant-sheaf`.
  This maps every term and differential, not just cohomology or degree zero.
  A direct attempt to use `AddCommGrpCat` has no tensor-monoidal instance in this
  import environment; it must not be confused with cartesian tensor. The lifted
  integer-module specialization avoids that error and the small-ring universe
  instance mismatch of unlifted ℤ.

Dependency declarations read and reused:

- `def-weil-pbc-etale-site`: `Mathlib.AlgebraicGeometry.Sites.Etale`,
  `AlgebraicGeometry.Scheme.smallEtaleTopology` and its underlying `Scheme.Etale`.
- `def-kun-constant-sheaf`: `Mathlib.Algebra.Homology.Additive`,
  `CategoryTheory.Functor.mapHomologicalComplex`, applied to `constantSheaf`.
- `def-weil-pbc-derived-categories`: `Sheaf.AlgebraicGeometry.DerivedCategories`,
  its documented `AlgebraicGeometry.Etale.DerivedCategoryModule` encoding; the
  abbreviation is defined in `WeilConjectures.SixFunctors.Etale.Derived.Coefficients`.
- `def-pc-cochain-complex-modules`: `Mathlib.Algebra.Homology.HomologicalComplex`,
  `CochainComplex`.
- `def-pc-acyclic-complex-modules`: its Mathlib match, `HomologicalComplex.Acyclic`
  in `Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex`.
- `def-pc-quasi-iso-modules`: its Mathlib match, `QuasiIso` in
  `Mathlib.Algebra.Homology.QuasiIso`.
- `def-pc-tensor-complex-sheaves`: `CochainComplex.mapBifunctor` in
  `Mathlib.Algebra.Homology.BifunctorShift`.
- `def-pc-kflat-complex`: `CochainComplex.IsKFlat` and `IsKFlatResolution` in
  `Sheaf.Algebra.Homology.KFlat`; read the full independent-universe signature.
  This is related to upstream `kFlat` by the cone criterion just explained, not
  redefined with an unproved data choice.
- `lem-pc-kflat-resolution`:
  `Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients`,
  `CochainComplex.exists_isKFlatResolutionIndependentCoefficients`;
  all four conclusion clauses were read (K-flat, flat terms, quasi-isomorphism,
  degreewise epi). It is not necessary to construct another resolution to reuse
  the already-existing derived tensor.

Edge cases checked: zero complexes and the zero ring remain allowed; the empty
scheme remains allowed; complexes may be unbounded in both directions and each
anti-diagonal may have infinitely many summands; the tensor is still a coproduct.
Negative p gives the required parity sign. The ordinary total tensor of complexes concentrated in degree zero gives ordinary
module tensor. Their derived tensor may have higher Tor; no flatness is assumed. No finite-flat-dimension hypothesis is added. Universe parameters
are those of the recorded derived-category encoding; integer coefficients require
lifting the coefficient ring, not imposing an equality of site universes.

Searches:

- `msearch.py ... leanfinder "Derived tensor product of unbounded complexes of etale
  sheaves computed by K-flat resolutions"`: eight results, all Tor/Tor' and related
  degreewise results; none is this unbounded sheaf-derived tensor.
- `msearch.py ... loogle "CochainComplex.mapBifunctor, DerivedCategory.Q"`: zero hits.
- `msearch.py ... grep "derivedTensor|DerivedTensor|KFlat" Algebra/Homology`:
  zero hits in Mathlib for a derived tensor construction.
- `rg` of upstream `WeilConjectures` for `derivedTensor|DerivedTensor|KFlat`:
  found the exact `SixFunctors/Etale/Derived/Tensor.lean` construction and its
  generic K-flat monoidal machinery. Read that file in full, the derived monoidal
  instances, and the one-sided comparison signatures and docstrings.
- Search for the blueprint id in upstream: no direct id attachment; the
  construction is present under its mathematical name.
- `rg` of `lean/Sheaf`: found the pro-etale `Scheme.derivedTensor`, scheme derived
  tensor structure, and ringed-site descent interfaces, which are not duplicate
  definitions to introduce for this etale node. The etale upstream declaration
  has the exact category recorded in this item's dependency.
- `dag/lean_names_upstream.json` lookup: the older inventory names the pro-etale
  tensor, but direct upstream source contains the etale definition too.

Validation: the sandbox scratch probe checks the Λ-module specialization against
`Etale.DerivedCategoryModule`, the termwise constant-complex functor, the lifted
integer specialization, its coefficient forgetful transport, and the existing
K-flat counit signatures. It is compiled exclusively with the prescribed
`scompile.py`. No scratch probe is delivered as a library module. No new theorem
or proof is delivered. No node faults or statement disputes were found.


## Second reading by NB

Independently read the full sandbox node, its blueprint source
`sec-smooth-purity/sk-prop-sf-kunneth-ordinary/def-kun-derived-tensor.md`, the upstream
`SixFunctors/Etale/Derived/Tensor.lean` (including all surrounding variables and the
body), `Derived/Coefficients.lean`, and the nine dependency statements and records.
The source is the blueprint markdown, not a Stacks lemma with additional ambient
hypotheses. The expanded node faithfully spells out that source's tensor convention.

Object/hypothesis/clause checklist, in source order:

1. Commutative ring Λ and arbitrary scheme T: specialize `A` to
   `ModuleCat.{u + 1} Λ`, with `(Λ : Type (u + 1)) [CommRing Λ] (T : Scheme.{u})`.
   The generic declaration has abelian, Grothendieck, symmetric monoidal, closed,
   monoidal-preadditive and functorial-flat-resolution assumptions. The scratch
   specialization synthesizes them all from these binders. Verdict: exact; no
   Noetherian, characteristic, torsion, nonempty or flatness assumption on Λ.
2. Small etale site and constant coefficient ring: the declaration explicitly uses
   `Sheaf T.smallEtaleTopology A`. Opened Mathlib's `smallEtaleTopology` and the
   recorded `DerivedCategories.lean`: their coefficient encoding is precisely
   module-valued sheaves, with tensor obtained by sheafifying module tensor.
   Modules over the sheafified constant ring correspond to these sheaves: the
   constant-presheaf action extends uniquely by sheafification. Verdict: same
   category and tensor, not global-section modules or the pro-etale site.
3. Unbounded derived category, cochain complexes, acyclicity and quasi-isomorphisms:
   `Etale.DerivedCategoryModule Λ T` unfolds to the three categories in the
   recorded signature. Read `CochainComplex`, `HomologicalComplex.Acyclic`
   (`∀ i, ExactAt i`) and `QuasiIso` (isomorphisms on homology for every i).
   Integers index all degrees. `Q` is the localization at these maps; `Qh` uses
   the intervening homotopy category. Verdict: all clauses, unbounded.
4. Ordinary direct-sum total tensor and differential: Mathlib
   `HomologicalComplex.tensorObj` is `mapBifunctor K L (curriedTensor C) c`.
   Its graded tensor is the coproduct on p+q=n. Read the integer
   `ComplexShapeSigns` instance and `ε_up_ℤ`, and the symmetry sign
   `(p*q).negOnePow`. These give first differential sign 1, second sign (-1)^p,
   and exactly the node's signed symmetry. Verdict: exact, no product totalization.
5. K-flat acyclic test: opened `Sheaf/Algebra/Homology/KFlat.lean` and its
   independent-site/coefficient universe binders. `IsKFlat` tests acyclic F in
   `mapBifunctor F K`; symmetry exchanges the factors. The upstream
   `MorphismProperty.kFlat` tests quasi-isomorphisms under both tensor functors.
   These conditions agree: cones detect quasi-isomorphisms, additive total tensor
   commutes with cones, and conversely one tests 0 → F for acyclic F. No
   termwise-flat or bounded hypothesis is substituted. Verdict: equivalent
   formulations of the same K-flat notion, not a private replacement.
6. Representatives C₁,C₂ and a K-flat quasi-isomorphism P → C₁: the recorded
   generic resolution theorem has all four stated properties (K-flat, flat terms,
   quasi-isomorphism, degreewise epi); the latter two extra resolution properties
   impose no restriction on inputs. The existing upstream construction already
   supplies its K-flat localization resolution. Verdict: arbitrary inputs covered.
7. Formula Q(P tensor C₂): read `DerivedCategory.tensorLeftCounit` and
   `isIso_tensorLeftCounit` in `DerivedCategory/Monoidal/Shift.lean`.
   Their comparison is `Qh(P) tensor^L Qh(C₂) → Qh(P tensor C₂)`, invertible
   whenever P is K-flat. `quotientCompQhIso` identifies this with Q, and the
   localized quasi-isomorphism identifies Q(P) with K₁. Verdict: exact formula
   up to the canonical derived-category isomorphism meant by representation.
8. Independence: `derivedTensor` is concretely `curriedTensor _` of the
   K-flat-derived monoidal structure, with `isLeftDerivedFunctor₂_derivedTensor`.
   Opened `HasMonoidalDerivedCategory.lean`: its structure is supplied by the
   K-flat left derivability construction. Verdict: actual derived functor data,
   not arbitrary choice of a bifunctor or hollow data. No new independence
   theorem is introduced by this definition node.
9. Integer coefficients and termwise constant M: use the same tensor with
   `ModuleCat.{u + 1} (ULift.{u + 1} ℤ)`, transported by restriction along the
   integer ring equivalence and the equivalence of integer modules with abelian
   groups. `Functor.mapHomologicalComplex` of `constantSheaf`, with
   `ComplexShape.up ℤ`, maps every term and differential. Opened its definition
   in Mathlib `Algebra/Homology/Additive.lean`. Verdict: the final notation is
   this specialization; no concentration in degree zero is imposed.

Edge cases: empty scheme, zero ring, zero complexes, characteristic two and
arbitrary characteristic are admitted. There is no external index set; empty
coproducts are zero, and infinite integer anti-diagonals use direct sums. Degrees
0 and negative degrees have the prescribed signs. Unboundedness in both directions
is retained. The coefficient universe follows the already-recorded derived-category
encoding; small rings can be lifted, and no site object/morphism universe equality
is added. In particular, degree-zero derived inputs need not have degree-zero
output: higher Tor remains present.

Independent searches used different wording from the first reader:
`msearch.py ... leanfinder "Total left derived monoidal product on unbounded derived
category of module valued sheaves"` returned Tor/Tor' and sheaf monoidal results,
not an unbounded tensor definition. `msearch.py ... loogle
"DerivedCategory.tensorLeftCounit"` had no indexed hit. Direct `rg` for
`derivedTensor|totalLeftDerived|tensorLeftCounit` in the project and upstream
found this exact etale construction and distinct scheme/ringed-site constructions;
`rg` in Mathlib for `tensorObj|mapBifunctor` and in `ComplexShapeSigns.lean`
confirmed the ordinary tensor and signs. The upstream exact match is reused;
there is no new module, new node, dependency module, or statement correction to audit.

Mismatch repaired: the worker report's degree-zero sentence could incorrectly imply
that derived tensor of arbitrary degree-zero modules is ordinary tensor. Qualified
it to refer only to ordinary total tensor and explicitly retained higher Tor.
No mismatch in the node's existing declaration record was found; its signature is
verbatim from the source, with A and X bound by the surrounding variables. No Lean
or node changes were necessary. Existing upstream docstrings and bodies were read;
no new declarations, proofs or hollow definitions are delivered.
