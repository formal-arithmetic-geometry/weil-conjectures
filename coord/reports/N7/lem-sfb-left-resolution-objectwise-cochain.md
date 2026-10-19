## Worker report

Existing-declaration delivery for `lem-sfb-left-resolution-objectwise-cochain`.
The exact construction and augmentation already exist in
`WeilConjectures.FromJoel.Algebra.Homology.LeftResolution.Basic` on `slopmaster2`.
The primary recorded declaration is
`CategoryTheory.Abelian.LeftResolution.cochainComplexNatTransπ`.
Its companion declarations are listed in `lean.declarations`; their fully expanded
signatures were checked through `scompile.py`. No module is delivered, and only
`lean` changes in the copied node. No theorem is restated and no notion is redefined.
The source checkout and current published source read with `scompile.py --source`
agree. The UTC record date is from `date -u +%F`, which returns 2026-10-17.

In the following, unqualified left-resolution names have prefix
`CategoryTheory.Abelian.LeftResolution`.

Hypothesis correspondence:

- The abelian category A is `{A : Type uA} [Category.{vA} A] [Abelian A]`.
  `CategoryTheory.Abelian` supplies kernels, cokernels and zero morphisms.
- The preadditive category C with a zero object is
  `{C : Type uC} [Category.{vC} C] [Preadditive C] [HasZeroObject C]`.
  Preadditivity supplies the `HasZeroMorphisms C` required by the source.
  The existing construction only needs zero morphisms, so applying it to this
  C does not require any extra condition or a different category.
- The fully faithful functor is `{ι : C ⥤ A} [ι.Full] [ι.Faithful]`.
  In particular `ι.PreservesZeroMorphisms` is inferred by Mathlib's
  `Functor.preservesZeroMorphisms_of_full` (Limits/Preserves/Shapes/Zero.lean).
  Additivity of ι, idempotent completeness of C, and finite coproducts in C
  are not assumed by the source or the node and are not added.
- The left-resolution datum is `(Λ : CategoryTheory.Abelian.LeftResolution ι)`.
  Its fields are `F : A ⥤ C`, `π : F ⋙ ι ⟶ 𝟭 A`, and
  `epi_π_app (X : A) : Epi (π.app X)`. Thus it is exactly the pair with
  epimorphic components in the node; there is no arbitrary resolution map.
- The zero-preservation assumption on F is `[Λ.F.PreservesZeroMorphisms]`.
  The source construction and quasi-isomorphism actually hold without this
  extra restriction, so they apply in particular to precisely the stated
  datum. No reduction or idempotent-completeness hypothesis is needed here:
  the node uses the *datum notion* from reduced-api, not its reduction theorem.
- The four object and morphism universes uA, vA, uC, vC are independent.
  The scratch consumer explicitly binds them and compiles for all four;
  there is no universe equality or restriction to small categories.

Clause correspondence:

- R is exactly `Λ.cochainComplexFunctor : A ⥤ CochainComplex C ℤ`, defined
  as `Λ.chainComplexFunctor ⋙ ComplexShape.embeddingDownNat.extendFunctor _`.
  Its object is the abbreviation `Λ.cochainComplex X`. Both functor laws are
  supplied by these existing functors, with no choices of unrelated objects.
- For q>0, R(X)^q is a zero object: the instance
  `instIsStrictlyLECochainComplexOfNatInt` has type
  `(Λ.cochainComplex X).IsStrictlyLE 0`. By
  `CochainComplex.isStrictlyLE_iff` this means exactly
  `∀ (q : ℤ), 0 < q → IsZero ((Λ.cochainComplex X).X q)`.
  It is strict termwise support, not merely vanishing cohomology.
- Degree zero is identified with `Λ.F.obj X` by
  `cochainComplexXZeroIso`; degree -1 is identified with
  `Λ.F.obj (kernel (Λ.π.app X))` by `cochainComplexXNegOneIso`.
  These are the canonical identifications inherent in extension by zero,
  not weaker existence claims about other objects.
- The formula for d^(-1) is precisely `cochainComplex_d_neg_one_zero`:
  `ι.map ((Λ.cochainComplex X).d (-1) 0)` equals
  `ι.map (Λ.cochainComplexXNegOneIso X).hom ≫
  Λ.π.app (kernel (Λ.π.app X)) ≫ kernel.ι (Λ.π.app X) ≫
  ι.map (Λ.cochainComplexXZeroIso X).inv`.
  After the named canonical identifications this is the node's formula;
  faithfulness gives uniqueness of this lifted differential.
- The higher recursion is the exact recorded Mathlib construction
  `Λ.chainComplex X`, with
  `chainComplexXIso X n : (Λ.chainComplex X).X (n+2) ≅
  Λ.F.obj (kernel (ι.map ((Λ.chainComplex X).d (n+1) n)))`, and
  `map_chainComplex_d`. Transport through `HomologicalComplex.extendXIso`
  and `extend_d_eq` along `embeddingDownNat` changes chain degree m to
  cochain degree -m. Setting n=m-1 for m≥1 gives exactly
  R(X)^(-m-1)=F(ker ι(d^(-m))) with the displayed augmentation followed
  by kernel inclusion. The map lifts are `ι.preimage` of those composites.
- On f:X→Y, the functor uses `Λ.chainComplexMap f` followed by
  `HomologicalComplex.extendMap`. The formulas `chainComplexMap_f_0`,
  `chainComplexMap_f_1`, and `chainComplexMap_f_succ_succ` state that its
  components are F(f) and F of the induced kernel maps. `extendMap_f`
  identifies them in negative cochain degrees; `extendMap_f_eq_zero`
  gives zero components in positive degrees. This is the stated map action.
- The augmentation is the actual cochain map `Λ.cochainComplexπ X` from
  `(ι.mapHomologicalComplex (ComplexShape.up ℤ)).obj (Λ.cochainComplex X)`
  to `(HomologicalComplex.single A (ComplexShape.up ℤ) 0).obj X`.
  `HomologicalComplex.single` is the stated X[0] (a single complex, not a
  shift of an unspecified complex).
- Its component in degree zero is `cochainComplexπ_f_0`:
  `ι.map (Λ.cochainComplexXZeroIso X).hom ≫ Λ.π.app X ≫
  (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 X).inv`.
  Under the canonical source and target identifications this is π_X.
  All other target terms are zero; `HomologicalComplex.mkHomToSingle`
  is the construction in the existing definition of the augmentation.
- Naturality is the natural transformation `cochainComplexNatTransπ` of
  type `Λ.cochainComplexFunctor ⋙ ι.mapHomologicalComplex _ ⟶
  HomologicalComplex.single A (ComplexShape.up ℤ) 0`, whose app is
  `Λ.cochainComplexπ X`. Its naturality field applies to every f:X→Y.
- Every component is a quasi-isomorphism: the recorded instance
  `instQuasiIsoIntCochainComplexπ` has type
  `QuasiIso (Λ.cochainComplexπ X)` for every X. The natural augmentation
  component is definitionally this map. The source additionally supplies
  `instQuasiIsoIntAppHomologicalComplexUpCochainComplexNatTransπ`, of type
  `QuasiIso (Λ.cochainComplexNatTransπ.app X)`, checked in the scratch probe.
  QuasiIso means isomorphisms on all integer cohomology objects, not
  merely at degree zero or for a selected object.
- Strict support after applying ι is given by the recorded Mathlib
  `HomologicalComplex.map_isStrictlySupported`, with K=Λ.cochainComplex X,
  F=ι and e=ComplexShape.embeddingUpIntLE 0. This immediately has the
  type `CochainComplex.IsStrictlyLE
  ((ι.mapHomologicalComplex (ComplexShape.up ℤ)).obj
  (Λ.cochainComplex X)) 0`. The scratch consumer confirms instance
  synthesis with exactly the node's hypotheses. It does not assume ι
  additive; fullness gives zero preservation, which suffices to preserve
  zero objects via the equation id=0.

Dependencies used and read, including their full signatures/docstrings:

- `def-sp-abelian`: `CategoryTheory.Abelian`,
  `Mathlib.CategoryTheory.Abelian.Basic` (class and derived zero/biproducts).
- `def-weil-preadditive-category`: `CategoryTheory.Preadditive`,
  `Mathlib.CategoryTheory.Preadditive.Basic` (abelian Hom groups and bilinearity).
- `def-weil-abstract-derived-category`: its Mathlib encoding uses
  `CochainComplex`, `QuasiIso`, and `DerivedCategory`; the cochain and
  quasi-isomorphism parts are from `Mathlib.Algebra.Homology.HomologicalComplex`
  and `Mathlib.Algebra.Homology.QuasiIso`, reexported by the existing source.
  No derived-category localization or `HasDerivedCategory` is needed here.
- `lem-sfb-left-resolution-reduced-api`: its recorded Mathlib declaration
  `LeftResolution.reduced`, `Mathlib.Algebra.Homology.LeftResolution.Reduced`,
  was read with its instance and the underlying `LeftResolution` structure
  from `Mathlib.Algebra.Homology.LeftResolution.Basic`. The item uses that
  structure for a given datum, and does not invoke the reduction theorem.
- Proof dependencies `lem-sfb-left-resolution-chain-complex-functor` and
  `lem-sfb-left-resolution-chain-exactness` have exact Mathlib matches
  `LeftResolution.chainComplexFunctor` and `exactAt_map_chainComplex_succ`
  in `Mathlib.Algebra.Homology.LeftResolution.Basic`. Their signatures,
  recursion, chain-map formulas and exactness argument were read.
- `lem-sfb-left-resolution-complex-extension` uses the recorded Mathlib
  `extendXIso`, `extend_d_eq`, `extendFunctor`, `extendMap_f`,
  `extendMap_f_eq_zero`, `extend_exactAt_iff`, and the `embeddingDownNat`
  strict-support instance, in `Embedding.Extend`, `Embedding.ExtendHomology`
  and `Embedding.CochainComplex`. These are the source's actual construction.

The source also already implements the node's six proof steps: the Mathlib
chain complex iterates kernel epimorphisms; extension along n↦-n gives the
cochain functor; the kernel condition produces the augmentation; π naturality
and kernel-map functoriality give naturality. In degree zero the augmented
short complex is exact because π on the kernel is epic and π_X is epic.
In negative degrees exactness is transported from
`exactAt_map_chainComplex_succ`; in positive degrees all terms are zero.
This gives QuasiIso at every degree. Finally extension has strict support,
and the zero-preserving functor ι preserves that strict support.
All these are existing proofs; no proof or sorry is delivered.

Edge cases checked: q=0 and q=-1 use the two explicit identifications and
first differential equation; q>0 uses termwise IsZero; q=-2 uses the first
recursive kernel; arbitrary negative q uses the chain recursion. X=0 is
allowed: the assumed zero-preservation of F sends the identity-zero equation
to one for F(0), and the kernel recursion continues with zero objects. No
nonzero-object, boundedness, chosen bound, or finite-coproduct hypothesis
occurs. Identity and zero morphisms are allowed; their chain maps are given
by `chainComplexMap_id` and `chainComplexMap_zero`. Empty categories do not
supply the assumed zero object; no extra inhabitedness is imposed.

Searches performed:

- `msearch.py leanfinder`: "Functorial cochain complex left resolution with
  quasi-isomorphic augmentation and zero terms above degree zero". Eight
  hits, led by Mathlib `LeftResolution.chainComplexFunctor`, chainComplex
  and the datum structure; no exact cochain result in Mathlib.
- `msearch.py loogle`: "LeftResolution cochainComplexFunctor QuasiIso".
  Zero hits; `LeftResolution` is not resolved by the Loogle environment.
- `msearch.py grep`: "cochainComplexFunctor|cochainComplexNatTransπ" in
  Algebra/Homology. Five unrelated factorization hits; no left-resolution
  cochain declaration in Mathlib.
- `msearch.py leansearch`: "cochain complex left resolution quasi-isomorphic
  natural augmentation strictly supported nonpositive degrees". Eight
  chain-resolution/augmentation/embedding hits, no exact Mathlib cochain match.
- `rg` in `WeilConjectures` for cochainComplexFunctor, cochainComplexNatTransπ
  and LeftResolution located this exact upstream source and its uses in
  CochainComplexMinus. Reading the complete Basic.lean and current source
  through `scompile.py --source` confirms the exact match.
- `rg` for the item id in `WeilConjectures` found no tagged declaration;
  the existing source nevertheless gives the exact mathematical construction.
- `rg` in `lean/Sheaf` for these names and objectwise/cochain-resolution
  variants found consumers but no second definition or exact duplicate theorem.
  The same exact names/item id have no match in `dag/lean_names_upstream.json`.

Validation: the final `scratch/ExistingChecks.lean` was compiled using the
prescribed `scompile.py` wrapper. Both sandbox and library probe passes are
clean, with no warnings or errors. Its examples synthesize QuasiIso and both
strict-support assertions under all of the node's hypotheses and four explicitly
bound universes. It checks all recorded cochain declarations and
`HomologicalComplex.map_isStrictlySupported`. `#print axioms` for the functor,
augmentation, quasi-isomorphism instance, strict-support instance and mapped
support instance reports only propext, Classical.choice, Quot.sound.
The scratch files are not delivered. There are no new nodes, dependency-module
repairs, statement corrections, or STATEMENT-DISPUTED findings.

## Second reading by N7

On a second pass, I reread the copied node beside the existing source and the
expanded consumer signatures. I checked separately the given datum versus the
reduction theorem (so no idempotent-completeness assumption is imported), the
canonical degree-zero and degree-minus-one identifications, the higher kernel
recursion after n↦-n, the actual augmentation component π_X, all-object
naturality, all-degree quasi-isomorphism, and strict termwise support in C and A.
The identified mismatch in the initial draft approach was redundancy: writing
another proposition for the conjunction would restate facts already supplied
by upstream instances. It was replaced by the existing record. The source's
weaker requirement HasZeroMorphisms C is satisfied by the node's preadditivity,
and its independent universes cover all stated categories. No mathematical
statement changes were necessary. This is a worker self-check; the independent
maintainer review is the review specified by this dispatch brief.

Dry-run repair: the generated existing-name probe put the long automatically
named NatTrans QuasiIso instance on a line over 100 characters. The record now
names the shorter existing `instQuasiIsoIntCochainComplexπ`, which supplies
the identical property because the natural augmentation app is definitionally
`cochainComplexπ X`. The source and scratch consumer confirm both versions.
