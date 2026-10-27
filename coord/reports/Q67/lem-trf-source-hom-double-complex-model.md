## Worker report

The module `Sheaf.Algebra.Homology.SourceHomDoubleComplexModel` states
`CochainComplex.source_hom_double_complex_model`. Its only proof is `sorry`.
No definitions, new nodes, dependency repairs, or statement corrections are needed.
The mathematical statement is unchanged. The only extra statement dependency is the
already landed `def-sc-module-total-hom-complex`, whose ordinary-module presentation
of the Hom complex is used directly.

Hypothesis and conclusion correspondence:

- A commutative ring is `(A : Type u) [CommRing A]`. Modules and all morphisms remain
  in `ModuleCat.{u} A`, so all displayed identifications are A-linear. The universe
  `u` is arbitrary; it is the ambient universe containing the ring and modules.
- The integer cochain complex M is `M : CochainComplex (ModuleCat.{u} A) ℤ`.
  The upper bound is the arbitrary integer `u₀`; `hM` says precisely
  `∀ a, u₀ < a → IsZero (M.X a)`. There is no lower bound, projectivity,
  finite-generation, or Noetherian assumption. N is an arbitrary `ModuleCat` object.
- Existence of the nonnegative injective resolution is the first conjunct:
  `∃ I, ∃ s : (singleFunctor ... 0).obj N ⟶ I, QuasiIso s ∧ ...` with
  every term injective and every negative-degree term zero. This states the
  integer-indexed version explicitly rather than concealing extension by zero.
- The second conjunct quantifies over EVERY integer complex I and augmentation s
  satisfying exactly those resolution properties. It is independent of the
  witnesses in the first conjunct; no special chosen resolution is imposed.
- The double complex is `D : HomologicalComplex₂ ... (up ℤ) (up ℤ)`.
  This is an outer complex of inner complexes: the chain-map property of each
  outer differential is exactly commutation of the two differentials. The two
  square-zero properties are included in its complex structures.
- First-quadrant vanishing is `∀ i b, i < 0 ∨ b < 0 → IsZero ((D.X i).X b)`.
  For nonnegative i,b, the isomorphism `e i b hi hb` identifies the term with
  `ModuleCat.of A (M.X (u₀-b) →ₗ[A] I.X i)`. Isomorphisms specify identification
  of categorical objects without requiring particular underlying type encodings.
  Their domain is the actual D term; there is no arbitrary coefficient map.
- The first formula conjugates `(D.d i (i+1)).f b` by e and evaluates it on f;
  its value is exactly `(I.d i (i+1)).hom.comp f`, i.e. d_I after f.
- The second formula conjugates `(D.X i).d b (b+1)` by e, with value
  `(b-u₀+1).negOnePow • (f.comp (M.d (u₀-(b+1)) (u₀-b)).hom)`.
  Thus precomposition is by the stated source differential and uses the stated
  sign, independent of i. Maps incident to terms outside the quadrant are
  necessarily zero, since those terms are zero objects.
- T is the EXISTING `CochainComplex.moduleHomComplex M I`, whose terms are
  `HomComplex.Cochain M I t`. These are the full products of homogeneous linear
  maps in integer degrees, not direct sums or a truncated source. Its differential
  is the existing `HomComplex.δ_hom A M I`, with d_I f - (-1)^t f d_M.
  On the one-object identity-covering ringed site this is the module presentation
  of the recorded `CategoryTheory.homComplex`; there are no restriction or descent
  data to add. Its ordinary-module definition already has a DAG node and module.
- The translated complex Q is equipped with `q t : Q.X t ≅ Tot(D).X (t+u₀)`.
  The equality `Q.d ... ≫ q.hom = q.hom ≫ Tot(D).d ...` specifies the unchanged
  total differential, with no signed-shift substitution. This characterizes Q up
  to the displayed degreewise identification.
- The complex isomorphism is `φ : moduleHomComplex M I ≅ Q`.
  For EVERY diagonal `i+b=t+u₀` in the quadrant, the equality specifies that
  `φ.inv.f t` after `q.inv` sends the total coprojection of f to
  `HomComplex.Cochain.single (ModuleCat.ofHom (e.hom f)) t`.
  The single cochain is supported at source degree `a=u₀-b` and target degree i;
  the diagonal equation implies `a+t=i`. This is the inverse finite-coordinate
  reindexing, including zero on every other coordinate. Because the maps are
  linear and coprojections generate the total, it fixes the inverse completely.
  It is stronger than a bare uncharacterized existence of a complex isomorphism
  only in the sense that it includes the coordinate characterization expressly
  required by the node.
- The final `Nonempty` is an isomorphism IN `DerivedCategory (ModuleCat A)`, from
  `DerivedCategory.Q.obj Q` to the existing `ordinaryModuleDerivedInternalHom A`
  evaluated at `(op (DerivedCategory.Q.obj M), DerivedCategory.Q.obj N[0])`.
  The dependency's ordinary-module presentation is the same K-injective-derived
  closed internal Hom; it is not an arbitrary bifunctor. The natural-language
  proof explains that this is obtained by localization of φ and the K-injective
  Hom comparison, exactly as the source states.

Dependency declarations read and used:

- `def-weil-abstract-derived-category`: `DerivedCategory`, `HasDerivedCategory`,
  and `DerivedCategory.Q`, from `Mathlib.Algebra.Homology.DerivedCategory.Basic`.
- `def-sp-injective-resolutions`: `CategoryTheory.Injective` and
  `CategoryTheory.InjectiveResolution`, from the recorded Mathlib Basic/Resolution
  modules. The statement expands the integer resolution into the same injective
  terms and quasi-isomorphism data. Read also `InjectiveResolution.cochainComplex`
  and `InjectiveResolution.ι'` in `Mathlib.CategoryTheory.Abelian.Injective.Extend`.
- `def-sp-double-complex-total`: the recorded upstream
  `WeilConjectures.CategoryTheory.DoubleComplexTotal`; Mathlib's
  `HomologicalComplex₂`, `.total`, `.ιTotal` and their first-quadrant convention.
- `def-pur-hom-complex`: `CategoryTheory.homComplex`,
  `CategoryTheory.homComplexFunctor` and `homComplex_exists`, from
  `WeilConjectures.Algebra.Homology.HomComplex`. Their full product and sign
  specification was read; the already existing ordinary-module presentation
  is used below.
- `def-sc-module-total-hom-complex`: `CochainComplex.moduleHomComplex`,
  `moduleHom_shape` and `moduleHom_square`, from
  `WeilConjectures.Algebra.Homology.ModuleHomComplex`.
  The existing `HomComplex.Cochain.single` supplies the coordinate description.
- `def-pur-derived-internal-hom`: `CategoryTheory.ordinaryModuleDerivedInternalHom`
  from `Sheaf.Algebra.Homology.OrdinaryModuleDerivedInternalHom`.
  Read its underlying generic `derivedInternalHomOfUniverses` and comparison
  theorem in the publicly imported `DerivedInternalHomOfUniverses` module.
- Proof-only imports: `Mathlib.Algebra.Category.ModuleCat.EnoughInjectives`
  (`ModuleCat.enoughInjectives`); `Mathlib.CategoryTheory.Abelian.RightDerived`
  (the injective-resolution existence and degree-zero comparison leaf); and
  `Mathlib.Algebra.Homology.HomotopyCategory.KInjective`
  (`CochainComplex.isKInjective_of_injective`). These are the recorded Mathlib
  leaves and remain imports for stage 3.

Sources checked directly: `literature/stacks-project/injectives.tex`,
`remark-ext-from-filtered-complex`; `derived.tex`,
`lemma-injective-resolutions-exist` and `lemma-bounded-below-injectives-K-injective`;
`homology.tex`, `definition-associated-simple-complex`; `more-algebra.tex`,
`section-hom-complexes`. In particular, the total sign is (-1)^i and the Hom sign
is -(-1)^t. Their combination with the b-dependent sign is correct.

Edge cases checked mathematically before finalizing the signature:

- Any negative u₀ is allowed; e.g. u₀=-1,t=1 leaves the one pair (i,b)=(0,0),
  corresponding to a=-1. No natural-number coercion excludes this case.
- When t+u₀<0, there is no nonnegative diagonal pair and the total is zero;
  every Hom factor is zero because a>u₀ or a+t<0. Thus the isomorphism is valid
  even though its coprojection characterization has an empty index family.
- M=0, N=0 (including a nonzero acyclic injective resolution), and the zero ring
  are admitted. The result uses zero objects, not equality of object encodings.
- Characteristic two has the same sign formulas, whose negative signs then agree.
- M may be unbounded to the left and have arbitrary nonprojective, infinitely
  generated terms. In each degree only the finite interval [-t,u₀] contributes.
- For u₀ odd, the unchanged-differential equation avoids the signed-shift error.
  At i=0 or b=0 the outside terms are zero and do not impose extra conditions.

Searches for an existing full result (all msearch calls use Q67 and this item):

- `leanfinder`: "The Hom complex from a bounded above complex to a module injective
  resolution is the translated total complex of a signed first quadrant double
  complex". Eight hits, including `CochainComplex.cm5b.I`,
  `InjectiveResolution.ofCocomplex`, `.ι'`, `.cochainComplex` and `.ι`, and the
  K-injective proof auxiliary. These supply resolutions, not this signed total
  comparison or its translation.
- `loogle`: `CochainComplex.moduleHomComplex, HomologicalComplex₂.total`.
  Zero hits; the external Mathlib service does not index the project declaration
  `moduleHomComplex`, so that part supplies no absence evidence.
- `grep` in Mathlib `Algebra/Homology`:
  `HomComplex.*total|total.*HomComplex|[Hh]om.*double.*complex`. Zero hits.
- `leansearch`: "A bounded above source complex and an injective resolution of a
  module give a signed first quadrant Hom bicomplex computing derived Hom".
  Eight hits, all injective-resolution or right-derived-functor constructions;
  no signed bicomplex/coordinate comparison.
- `rg` in both `lean/WeilConjectures` and `lean/Sheaf` for the item id and
  `HomComplex.*total|total.*HomComplex`: no item declaration; found
  `HomTotalTriangularResigning.lean`, whose theorem is group-valued, uses the
  opposite index order and triangular multipliers, assumes source bound zero,
  and does not identify the ordinary-module RHom target. It is not this node.
- Follow-up source searches for `homComplex`, `moduleHomComplex`, internal Hom
  coordinates and `ordinaryModuleDerivedInternalHom` found the reusable
  declarations above. Name search for `source_hom_double_complex_model` and
  `sourceHomDoubleComplexModel` in both source trees and upstream name records
  found no collision. The prescribed upstream item-id search also found none.

Validation: scompile.py compiled the sandbox and its actual library module cleanly
(5.7 s and 7.0 s in the successful run). The first compiler run exposed a binder
precedence issue and the namespace of `Cochain.single`; these were repaired by
explicit proof binders and the full `HomComplex.Cochain.single` name. No diagnostic
commands remain. Delivery preflight and its additional compilation are run after
this report is recorded.

No STATEMENT-DISPUTED flag or source/node fault remains.

## Second reading by Q67

This is a separate review pass by the assigned dispatcher worker; the human's brief
prohibits starting another agent. It is not claimed as an independent worker review.
I reopened the node and final Lean text and traced their binders and conclusions.
The first conjunct supplies existence; the second independently quantifies over all
resolutions. The e binders are explicitly over i,b and proofs of nonnegativity,
so the term isomorphism is between module objects, rather than an accidental
isomorphism of a function type. The outer differential advances i and the inner
one advances b; its multiplier is b-u₀+1, not i+b-u₀+1. The translation q advances
both degrees by u₀ without a sign. The inverse coprojection equation gives exactly
a=u₀-b and i=a+t, inserting zero at all other source/target pairs. The last clause
retains the A-module-derived isomorphism with the declared ordinary-module RHom.
The upper-bound hypothesis is the only condition on M. No source statement changes
were necessary. No additional mismatch was found on this review pass.
