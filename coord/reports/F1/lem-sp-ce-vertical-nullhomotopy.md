## Worker report

The module `lean/Sheaf/CategoryTheory/CartanEilenbergVerticalNullhomotopy.lean`
states `CategoryTheory.cartanEilenberg_vertical_nullhomotopy`, with one `sorry`
and no definitions or auxiliary assertions. No statement correction, new node,
or dependency module is required.

Hypothesis and clause correspondence:

- The abelian category is `(A : Type u) [Category.{v} A] [Abelian A]`; both
  universes are explicitly declared, with no relation imposed between them.
- The cochain complexes are `(K L : CochainComplex A ℤ)`.
- The double complexes are `(I J : HomologicalComplex₂ A (ComplexShape.up ℤ)
  (ComplexShape.up ℕ))`. This is exactly the index convention of dependency
  `lem-sp-cartan-eilenberg-exists`. Natural vertical degrees represent extension
  by zero below zero; `hI` and `hJ` assert zero columns at every negative
  horizontal integer degree. Thus both double complexes are first quadrant.
- `eI` and `eJ` are augmentations from the same horizontal complexes placed
  in vertical degree zero by `CochainComplex.single₀` and
  `mapHomologicalComplex`. They simultaneously encode the maps in vertical
  degree zero and the fact those maps land in vertical cycles.
- The source augmented cycle, boundary, and horizontal-cohomology rows are
  exact resolutions: the three `QuasiIso` clauses of `hsource` use respectively
  `cyclesMap eI p`, `image.map (Arrow.homMk' ... (eI.comm ...))`, and
  `homologyMap eI p`. Their source complexes are concentrated in vertical
  degree zero with objects Z^p(K), B^p(K), H^p(K). Therefore quasi-isomorphism
  means the augmentation is monic, its image is the kernel of the first
  differential, and higher cohomology vanishes. No source injectivity is
  assumed. Boundaries are images of the differential from p-1 to p.
- The displayed sequences `0 → Z_I^p → I^{p,•} → B_I^{p+1} → 0` require
  no additional binder: with these canonical cycles and images they are
  automatically short exact in the abelian category `CochainComplex A ℕ`,
  hence degreewise short exact. The analogous boundary-cycle-homology
  sequences are also automatic. This uses the actual kernels and images,
  rather than separately chosen row objects and unrelated maps. Exactness
  of source augmented columns follows as an extension of the exact cycle
  and next-boundary rows, so it is not added as a stronger hypothesis.
- The corresponding target augmented rows are injective resolutions:
  `htarget` supplies the same three induced quasi-isomorphisms, while
  `hinjective` supplies injectivity of every cycle, boundary, and homology
  term. These are exactly the defining fields of `InjectiveResolution`,
  as used in the dependency's landed existence theorem. No hypothesis of
  enough injectives is needed, since the resolutions are already given.
  Injectivity of column terms follows from the degreewise split
  cycle-column-boundary short exact sequences, rather than being added.
- `R : I ⟶ J` is a morphism of bicomplexes, commuting with both differentials.
  `hR : eI ≫ R = 0` is precisely vanishing on the source augmentation.
- The first conjunct of the conclusion supplies null-homotopies on each
  induced cycle, boundary, and horizontal-homology row map. Each is a
  `Nonempty (Homotopy ... 0)`, expressing existence without choosing one.
- The second conjunct supplies `s : ∀ p : ℤ, Homotopy (R.f p) 0`.
  For q > 0, its component `(s p).hom q (q - 1)` is the required map
  I^{p,q} → J^{p,q-1}. The structure's `comm` field states exactly
  R = d_v s + s d_v (Lean writes composition in diagrammatic order).
  Its `zero` field restricts components to decreasing degree by one.
- The explicit clause `∀ p q, (s p).hom 0 q = 0` covers s^{p,0}=0.
  The missing degree -1 is the zero extension of a natural-indexed complex.
  This clause is also forced by `Homotopy.zero`; it adds no constraint.
- Horizontal compatibility is the last clause, for all p,p',q,q':
  `(s p).hom q q' ≫ (J.d p p').f q' =
  (I.d p p').f q ≫ (s p').hom q q'`. At p'=p+1 and q'=q-1
  this is s d_h = d_h s. Other components vanish by the two shape conditions,
  so quantifying over all indices neither strengthens nor weakens it.

Dependency declarations read and used:

- `def-sp-abelian`: Mathlib.CategoryTheory.Abelian.Basic,
  `CategoryTheory.Abelian` (class and its normal mono/epi fields).
- `def-sp-injective-resolutions`: Mathlib.CategoryTheory.Preadditive.Injective.Resolution,
  `CategoryTheory.InjectiveResolution` (cocomplex, degreewise injective, ι,
  quasiIso fields); Mathlib.CategoryTheory.Preadditive.Injective.Basic,
  `CategoryTheory.Injective` (extension along monomorphisms).
- `lem-sp-cartan-eilenberg-exists`: Sheaf.CategoryTheory.CartanEilenbergExists,
  `CategoryTheory.exists_cartanEilenberg_resolution`, full signature and proof
  docstring read. The module is imported, and its bicomplex, augmentation,
  boundary-image, and induced-row conventions are used verbatim; this is
  not an application of its existence result or an assumption that the
  source complex has injective terms.
- Mathlib.Algebra.Homology.Homotopy, `Homotopy`, full structure read:
  hom, zero, comm; no substitute homotopy notion is introduced.

Sources checked: the local literature tree does not contain derived.tex or
blueprint files on this machine. Read Stacks tags directly at
https://stacks.math.columbia.edu/tag/015I and
https://stacks.math.columbia.edu/tag/015H. They verify the index convention,
induced cycle/image/homology resolutions and canonical alternating sequences.
The null-homotopy detail is the node's supplied proof, attributed there to
Weibel Lemma 5.7.10; the Lean docstring records all three proof steps and
both named proof dependencies, including the prescribed-boundary induction.

Edge cases checked before writing: zero source or target bicomplex; R=0;
negative horizontal p; horizontal p=0 (B^0=0, induction starts here);
vertical q=0 (no fictitious predecessor, equation reduces to the next-degree
homotopy after d_v); rows concentrated in degree zero (exact augmentation
forces R=0 there); unbounded positive horizontal and vertical degrees;
arbitrary category and hom universes. K and L are not additionally assumed
bounded: exact induced augmented rows and the given first-quadrant support
force the relevant negative degrees to vanish. No field, ring, characteristic,
or global existence-of-injectives restriction is introduced.

Searches for existing declarations, using msearch.py with group F1/item
lem-sp-ce-vertical-nullhomotopy:

- leanfinder query: "A morphism of Cartan Eilenberg double complexes zero on
  augmentation admits a vertical null homotopy commuting with horizontal
  differentials". Eight hits: generic Homotopy.nullHomotopicMap component
  formulas, Homotopy.nullHomotopy and a bifunctor homotopy lemma. None state
  the Cartan--Eilenberg theorem or the horizontal-compatible existence claim.
- loogle query: "Homotopy, HomologicalComplex". Twelve hits: Homotopy,
  Homotopy.hom, refl, ofEq, symm and homotopy equivalence facts. These give
  the existing notion but not the theorem.
- msearch grep query: "cartanEilenberg|Cartan.Eilenberg|vertical.*[Hh]omot"
  restricted to Algebra/Homology: zero hits.
- leansearch query: "A Cartan Eilenberg resolution map vanishing on the
  augmentation has a vertical homotopy to zero compatible with horizontal
  differentials". Service unavailable: Internal Server Error.
- Local rg of the same names/concept and item tag in the source
  WeilConjectures tree, project lean/Sheaf, and dag/lean_names_upstream.json:
  only existing CartanEilenbergExists, CartanEilenbergProperties,
  CartanEilenbergLeftExactCohomology, and descriptive text in the source
  Grothendieck spectral-sequence module. No existing matching theorem, and
  no collision for CategoryTheory.cartanEilenberg_vertical_nullhomotopy.

Server compilation: scompile.py F1 lem-sp-ce-vertical-nullhomotopy with the
module path completed successfully in 1.4 seconds, exit code 0, no warnings.
All theorem proof work remains for stage 3. No STATEMENT-DISPUTED issue found.

## Second reading by F1

I reread the node and the complete Lean signature independently. The objects match
item by item: `(A : Type u) [Category.{v} A] [Abelian A]` is the abelian category;
`K L : CochainComplex A ℤ` are the two source complexes; `I` and `J` are
`HomologicalComplex₂ A (ComplexShape.up ℤ) (ComplexShape.up ℕ)`, hence have the
node's horizontal integer and vertical natural indices. The maps `eI` and `eJ` are
the stated augmentations from `single₀` complexes. `hI` and `hJ` explicitly impose
the first-quadrant zero condition in negative horizontal degrees.

The three conjuncts of `hsource` and `htarget` are exactly the induced cycle,
boundary-image, and horizontal-homology quasi-isomorphisms. `hinjective` gives
injectivity of each target cycle, boundary, and homology term, matching the
injective-row hypothesis. `R : I ⟶ J` and `hR : eI ≫ R = 0` state the double-complex
map and vanishing augmentation condition. The conclusion first quantifies the
three row `Nonempty (Homotopy ... 0)` clauses described by the node, then supplies
`s : ∀ p, Homotopy (R.f p) 0`; its two conjuncts are exactly `s^{p,0}=0` and the
all-index horizontal commutation equation. The `Homotopy` structure supplies the
vertical equation `R = d_v s + s d_v`, so no conclusion clause is omitted.

Edge cases checked are zero complexes and zero map, negative horizontal degrees,
`p = 0` (zero boundary), vertical degree `q = 0`, rows concentrated in degree
zero, arbitrary universes, and empty/zero objects. The natural vertical index and
the explicit `hI`/`hJ` conditions do not exclude any case in the node.

I searched Mathlib and the project with LeanFinder, Loogle, `msearch.py`, and `rg`
for Cartan--Eilenberg vertical null-homotopy declarations. Only generic
`Homotopy` constructions and the existing Cartan--Eilenberg existence theorem were
found; no matching theorem exists. The source tags 015H/015I and the Weibel lemma
were checked against the hypotheses and proof clauses. No mismatch was found, so
no Lean or node change was necessary. The module compiles cleanly with one `sorry`
proof as required for stage 2.
