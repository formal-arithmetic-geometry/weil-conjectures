## Worker report

The module `Sheaf.Algebra.Homology.InjectiveFinalKernelTruncation` states
`CochainComplex.exists_injective_final_kernel_truncation`, with its entire proof
left as `sorry`. There are no new definitions, nodes, dependency repairs, or
statement corrections. The source is Stacks Project, more-algebra.tex,
Tag 0A5T, proof of (3) implies (1), the displayed complex ending in J.
The docstring supplies all seven steps of the node's proof.

Hypotheses, in order:

- A commutative ring and module in a common universe are `{R : Type u}`,
  `[CommRing R]`, and `N : ModuleCat.{u} R`.
- The integer-indexed cochain complex is
  `I : CochainComplex (ModuleCat.{u} R) ℤ`; its bundled structure includes
  differentials and the square-zero identities.
- Vanishing in negative degrees is `hneg : ∀ j, j < 0 → IsZero (I.X j)`.
  In an additive category this is the intrinsic formulation of being a zero module.
- Injectivity of every term is `hinj : ∀ j, Injective (I.X j)`.
- The augmented exact sequence is encoded by the chain map
  `ε : (single (ModuleCat.{u} R) (ComplexShape.up ℤ) 0).obj N ⟶ I`
  and `[QuasiIso ε]`. The original map N → I^0 is
  `(singleObjXSelf (ComplexShape.up ℤ) 0 N).inv ≫ ε.f 0`.
  Chain-map compatibility gives its zero composite with the next differential.
  Because I has zero negative terms, H^0(I) is ker(d^0), with no nonzero
  incoming boundary. Thus the degree-zero quasi-isomorphism condition says
  exactly that this augmentation is injective with image ker(d^0).
  In positive degrees the condition says ker(d^j) = im(d^(j-1)); in negative
  degrees it is automatic. Conversely these augmented exactness conditions
  give precisely this quasi-isomorphism. There is no extra exactness assumption.
- The degree and its nonnegativity are `(d : ℤ)` and `(hd : 0 ≤ d)`.
- The final-kernel hypothesis is
  `hJ : Injective (kernel (I.d d (d + 1)))`.
  Mathlib's `ModuleCat.kernelIsoKer` identifies this kernel with the actual
  submodule kernel, compatibly with inclusion; it is not a different notion.
- `[HasDerivedCategory.{w} (ModuleCat.{u} R)]` chooses the morphism universe
  of the derived localization, as in the recorded size convention. It is not
  an additional mathematical restriction: `HasDerivedCategory.standard` always
  supplies a choice in the standard universe, and w remains arbitrary.

Clauses of the conclusion:

- `∃ L` supplies the requested integer-indexed cochain complex, including the
  existence of its differentials and their square-zero identities. This is an
  existence theorem, not a definition extracting unspecified data from sorry.
- The isomorphisms `a j hj hjd : L.X j ≅ I.X j` identify the graded terms
  for 0 ≤ j < d, and `b : L.X d ≅ kernel (I.d d (d + 1))` identifies the
  last term with J. Using explicit module isomorphisms avoids dependent casts
  while retaining the exact specified terms and all their maps.
- `ι : L ⟶ I` is the node's λ. The first conjunct says its retained
  components are precisely the homs of `a`, hence identities under those
  identifications. The second says `ι.f d = b.hom ≫ kernel.ι ...`, the inclusion.
- For j < 0 or d < j, the third conjunct gives both `IsZero (L.X j)` and
  `ι.f j = 0`. This states the support bound and the remaining components.
- The fourth conjunct ranges over consecutive retained degrees i,j and says
  `L.d i j ≫ a_j.hom = a_i.hom ≫ I.d i j`, exactly the retained differential.
  Its bounds are equivalent to 0 ≤ i < d-1 when j = i+1.
- The fifth conjunct treats i+1=d with 0 ≤ i < d. Composing the last
  differential with `b.hom` and the kernel inclusion equals the old
  differential after `a_i.hom`. Since the inclusion is monic, this uniquely
  specifies the corestriction I^(d-1) → J. The case exists exactly when d>0.
- The sixth conjunct sets every other consecutive differential to zero;
  nonconsecutive differentials are already zero by the cochain shape.
- `e` is a chain map from N[0] to L, and `e ≫ ι = ε` is λe=ε in
  categorical composition order.
- For d>0 the explicit component equation
  `e.f 0 ≫ (a 0 (le_refl 0) hpos).hom = ε.f 0` states e^0=ε under
  the specified retained-term identification.
- For d=0 the conjunct `IsIso (e.f 0)` gives the induced isomorphism N ≅ J
  after the single-complex identification and b. Its composite with the
  kernel inclusion is the original augmentation, by `e ≫ ι = ε`, so this
  is precisely the induced isomorphism, not an unrelated chosen one.
- `QuasiIso e` is the required augmentation quasi-isomorphism, and
  `∀ j, Injective (L.X j)` states termwise injectivity, including zero terms.
- The final existential is an actual isomorphism in D(R) from Q(N[0]) to Q(L),
  with `η.hom = DerivedCategory.Q.map e`. Thus it records the derived
  isomorphism induced by this augmentation, not just per-degree comparisons.

Dependency declarations read and used:

- `def-sp-injective-resolutions`: `CategoryTheory.Injective`, from
  `Mathlib.CategoryTheory.Preadditive.Injective.Basic`, used directly for
  I, J, and L. Also read `CategoryTheory.InjectiveResolution` in
  `Mathlib.CategoryTheory.Preadditive.Injective.Resolution`; its natural-number
  indexing is not substituted for the node's given integer-indexed resolution.
- `def-weil-abstract-derived-category`: `DerivedCategory`,
  `HasDerivedCategory`, `HasDerivedCategory.standard`, and `DerivedCategory.Q`
  from `Mathlib.Algebra.Homology.DerivedCategory.Basic`; also the underlying
  `HomologicalComplex.single`, `HomologicalComplex.QuasiIso`, and complex
  morphisms. All are the existing Mathlib constructions.
- `Mathlib.Algebra.Category.ModuleCat.Abelian` supplies the actual abelian
  category of modules and its kernels; `ModuleCat.kernelIsoKer` was read
  to check agreement with the node's submodule kernel.

Edge cases checked before writing and again against the final statement:

- d=0: the retained interval is empty, L has only J in degree zero,
  all differentials vanish, and the explicit `IsIso (e.f 0)` gives N ≅ J.
- d=1: the ordinary retained-differential clause is empty; the last
  differential clause applies at i=0, giving the required corestriction.
- d=2: the differential at 0 is retained and the one at 1 is corestricted.
- Negative degrees and degrees above d have zero terms and maps. The map
  at d is the inclusion and its outgoing differential is zero.
- N=0, a zero ring, and zero injective kernels are allowed; there is no
  nontriviality, positive-rank, Noetherian, or strictly-positive-d hypothesis.
- The ring and all module carriers use u; the derived morphism universe w
  is explicitly bound and independent. No auto-bound implicits are used.

Searches for an existing statement (all wrapper queries were run for this item):

- `msearch.py leanfinder`, query "An injective resolution truncated at an
  injective final kernel is a bounded injective complex with its augmentation
  quasi-isomorphism": eight hits, principally `InjectiveResolution.of`,
  `ofCocomplex`, `self`, and related injective-resolution instances. None
  includes the prescribed final kernel and compatible augmentation clauses.
- `msearch.py loogle`, query `CochainComplex.truncLE`: twelve hits, including
  `truncLE`, `truncLEXIso`, `truncLEXIsoCycles`, `ιTruncLE`, and its
  quasi-isomorphism API. These are partial construction tools rather than
  the node's whole statement. Their source signatures and docstrings were read.
- `msearch.py grep`, query `truncLE|truncLEXIsoCycles` in `Algebra/Homology`:
  25 hits on the truncation API, again no complete matching theorem.
- `msearch.py leansearch`, query "Smart truncation of an augmented injective
  resolution at an injective final kernel gives a bounded injective resolution
  with compatible augmentation": eight hits on resolution construction and
  `augmentTruncate`/`truncateAugment`; no matching statement.
- `rg` of both `lean/WeilConjectures` and `lean/Sheaf`, query
  `final.kernel|finalKernel|injective.*trunc|trunc.*injective`: hits concern
  Cartan–Eilenberg truncations, K-injective representatives, and derived
  comparisons, not this module-level final-kernel statement.
- `grep -rn lem-trf-injective-final-kernel-truncation lean/WeilConjectures`:
  no hits. The exact chosen declaration name was also searched in Mathlib,
  both library roots, and `dag/lean_names_upstream.json`: no existing name.

Validation: the complete module passed `scompile.py` in both the sandbox and
its final library module location, with no errors or warnings. No dispute or
node fault was found. Only the item's `lean` field is changed.

## Second reading by Q74

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
