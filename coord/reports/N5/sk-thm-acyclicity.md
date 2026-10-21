## Worker report

Existing match for both clauses; no Lean module, definition or proof is added.
Only the item's `lean` field changes. The current blueprint source
`literature/blueprint/main-20261015/blueprint/sec-proper-base-change/sk-thm-acyclicity/_section.md`
was read and agrees verbatim with the node. No repair note exists for the item.

The main attachment is
`CategoryTheory.Functor.isIso_rightDerivedFunctorPlusUnit_app_of_rightAcyclic`,
`WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusHomology`,
lines 101–104. Its public import of
`WeilConjectures.CategoryTheory.Abelian.RightDerived.Acyclic` supplies
`CategoryTheory.Functor.nonempty_rightDerivedObjIso_homology_of_acyclic`,
lines 305–308, recorded in `lean.declarations` for the first clause. Both modules
were also read from the current server with `scompile.py --source`.

### Hypotheses and clauses

- The node's categories A and B are the declarations' `C` and `D`, with
  `[Category* C] [Category* D] [Abelian C] [Abelian D]` in their section context.
  The object and morphism universes are unrestricted and independent.
- The node's functor v is `(F : C ⥤ D)`. Additivity is `[F.Additive]` and
  left exactness is `[PreservesFiniteLimits F]`. In abelian categories the
  latter is equivalent to preserving kernels for an additive functor; the
  recorded Mathlib interface is used, with no exactness assumption.
- The node assumes enough injectives in the abelian categories. The complex
  theorem assumes `[EnoughInjectives C]`; the resolution theorem assumes
  `[HasInjectiveResolutions C]`, inferred from `[Abelian C] [EnoughInjectives C]`.
  Neither needs enough injectives in D. They specialize directly to the node's
  hypotheses. This is the permitted existing-record specialization of a more
  general theorem with the identical conclusion (STATE ruling, 14:47).
- The object called F in the node is `{X : C}` in the resolution declaration.
  The resolution is `{I : CochainComplex C ℕ}` together with
  `(ι : (CochainComplex.single₀ C).obj X ⟶ I) [QuasiIso ι]` in its section
  context. Thus it is precisely a nonnegative augmented resolution: degree zero
  homology is X, all positive homology vanishes. Injectivity of the terms is
  not assumed.
- Termwise v-acyclicity of that resolution is
  `(hI : ∀ n, F.rightAcyclic (I.X n))`. The existing definition
  `rightAcyclic` means `∀ q : ℕ, IsZero ((F.rightDerived (q + 1)).obj A)`,
  precisely all strictly positive derived functors vanishing.
- The first conclusion, for `(q : ℕ)`, is
  `Nonempty ((F.rightDerived q).obj X ≅ ((F.mapHomologicalComplex _).obj I).homology q)`.
  Here the right side is H^q(vA). Symmetry of an isomorphism gives exactly
  the displayed H^q(vA) ≅ R^qvF. No extra naturality clause is asserted.
- For the second assertion, `(L : CochainComplex.Plus C)` means an integer
  indexed complex with `∃ a : ℤ, L.obj.IsStrictlyGE a`. This is termwise
  bounded below, with arbitrary integer lower bound, rather than an assumption
  only about the cohomology or a fixed lower bound of zero.
- Its termwise acyclicity is `(hL : ∀ n, F.rightAcyclic (L.obj.X n))`,
  now quantified over every integer n.
- The second conclusion is
  `IsIso (F.rightDerivedFunctorPlusUnit.app ((HomotopyCategory.Plus.quotient C).obj L))`.
  Mathlib defines `rightDerivedFunctorPlusUnit` as the transformation
  `F.mapHomotopyCategoryPlus ⋙ DerivedCategory.Plus.Qh ⟶
  DerivedCategory.Plus.Qh ⋙ F.rightDerivedFunctorPlus`.
  Consequently this is the specified canonical comparison from vL to Rv(L)
  in D⁺(D), with its actual direction and canonical map. It is an isomorphism
  of derived objects, not just unrelated isomorphisms on individual cohomology
  objects. The main attachment is therefore the derived assertion.
- `[HasDerivedCategory C] [HasDerivedCategory D]` are the chosen localization
  data from the recorded abstract-derived-category dependency. Standard choices
  always exist. They introduce neither a mathematical restriction on the
  abelian categories nor an equality between their universe levels.

The exact recorded signature is copied from the main declaration, from
`theorem` to immediately before `:=`. Its section context is described above;
no binders are introduced by this delivery.

### Dependency declarations read and used

- `def-sp-abelian`: `CategoryTheory.Abelian`,
  `Mathlib.CategoryTheory.Abelian.Basic`: preadditive, normal mono/epi,
  finite products, kernels, cokernels (lines 103–115).
- `def-sp-left-exact-additive`: `CategoryTheory.Functor.Additive`,
  `Mathlib.CategoryTheory.Preadditive.AdditiveFunctor` (42–46);
  `CategoryTheory.Limits.PreservesFiniteLimits`,
  `Mathlib.CategoryTheory.Limits.Preserves.Finite` (40–47);
  `CategoryTheory.Functor.rightDerived`,
  `Mathlib.CategoryTheory.Abelian.RightDerived` (110–118).
  The kernel/finite-limit equivalence was read at
  `Mathlib.CategoryTheory.Preadditive.LeftExact`, 117–124.
- `def-sp-injective-resolutions`: `CategoryTheory.Injective`,
  `Mathlib.CategoryTheory.Preadditive.Injective.Basic` (28–34), and
  `CategoryTheory.InjectiveResolution`,
  `Mathlib.CategoryTheory.Preadditive.Injective.Resolution` (38–56).
  `EnoughInjectives` is Basic 61–65; the resolution type includes its
  augmentation and quasi-isomorphism, and is not used to demand injectivity
  of the acyclic resolution's terms.
- `def-sp-acyclic`: `CategoryTheory.Functor.rightAcyclic`,
  `WeilConjectures.CategoryTheory.Abelian.RightDerived.Acyclic` (71–75).
  This is exactly the predicate used in both existing theorem signatures.
- `def-weil-abstract-derived-category`: `HasDerivedCategory`,
  `HasDerivedCategory.standard`, `DerivedCategory`, `DerivedCategory.Q`,
  `Mathlib.Algebra.Homology.DerivedCategory.Basic` (71–98).
- `def-weil-pbc-bounded-derived-subcategories`: `DerivedCategory.Plus`,
  `Mathlib.Algebra.Homology.DerivedCategory.TStructure` (203–204), with
  `TStructure.plus`, `Mathlib.CategoryTheory.Triangulated.TStructure.Basic`
  (263–264), and termwise bounded complexes `CochainComplex.plus`/`Plus`,
  `Mathlib.Algebra.Homology.CochainComplexPlus` (30–44).
- `lem-weil-pbc-right-derived-plus-injective`: `rightDerivedFunctorPlus`,
  `rightDerivedFunctorPlusUnit`, and its `IsRightDerivedFunctor` instance,
  `Mathlib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus` (33–55).
  `HomotopyCategory.Plus`, `HomotopyCategory.Plus.quasiIso` and
  `DerivedCategory.Plus.Qh` were read in their recorded Mathlib modules.
  The injective-complex computation is the instance in
  `Mathlib.Algebra.Homology.DerivedCategory.DerivabilityStructureInjectives`
  (378–393), used in the naturality argument of the existing main theorem.

Each dependency's node statement and Lean record or Mathlib match were read.
No private copy of any dependency is needed. No statement correction, disputed
statement, new node, or dependency repair is necessary.

### Edge cases

Degree q = 0 is included in the first theorem's natural-number binder;
`rightDerivedZeroIsoSelf` identifies R⁰v with v. Degree q = 1 requires no
further dimension shift. The zero object and zero complex are permitted:
`rightAcyclic.ContainsZero` is already provided, and zero complexes satisfy
any lower bound. The second theorem allows negative lower bounds and infinitely
many nonzero terms above the bound; there is no boundedness-above assumption.
No injectivity of the acyclic terms or Grothendieck condition is introduced.
The actual unit is inverted, not an arbitrary comparison. Its source and target
are in the full category D⁺(D). No universe restriction is added.

### Searches performed

- `msearch.py ... leanfinder` with “Acyclic resolutions compute right derived
  functors and a bounded below complex of acyclic objects computes the total
  right derived functor”: the service returned Mathlib candidates for derived
  functors and exact-functor transport. Repeated with “A bounded below complex
  of acyclic objects computes the right derived functor of a left exact additive
  functor”: 8 hits, including `Functor.rightDerived`, `mapDerivedCategory`,
  `mapDerivedCategoryFactors[h]`, `toRightDerivedZero`, and exact-functor Ext
  transport. None supplies the two assertions; exact transport assumes more
  than left exactness.
- `msearch.py ... loogle 'CategoryTheory.Functor.rightDerived'`: 12 hits,
  including `rightDerived`, `rightDerivedZeroIsoSelf`, injective vanishing,
  `toRightDerivedZero`, and induced natural transformations. These supply
  the definitions and degree-zero comparison, not the two acyclicity clauses.
- `msearch.py ... grep 'rightAcyclic|rightDerived.*[Aa]cyclic|[Aa]cyclic.*rightDerived'`:
  0 Mathlib hits.
- `rg` in `lean/WeilConjectures` and `lean/Sheaf` for the two expected theorem
  names, `rightDerivedFunctorPlusUnit.*rightAcyclic`, and `sk-thm-acyclicity`:
  the upstream Acyclic and PlusHomology modules contain the exact two results;
  many existing consumers use the canonical-unit theorem. No new module needed.
- `grep -rn 'sk-thm-acyclicity' lean/WeilConjectures`: found the resolution
  theorem's blueprint docstring at Acyclic line 303.
- `rg` in `dag/lean_names_upstream.json` for both expected theorem names:
  the resolution theorem is indexed; the unit theorem is found directly in
  the current source instead. Both declarations were read in full, including
  docstrings, section assumptions, proof, and the definition of the unit.

### Validation

The prescribed `deliver2.py --no-push` performs an `scompile.py` server probe
of both recorded existing declarations after importing PlusHomology, then
runs the server preflight. No delivered Lean file needs separate compilation.

## Second reading by N5

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
