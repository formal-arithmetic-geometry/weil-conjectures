## Worker report

The module `Sheaf.CategoryTheory.KInjectiveDerivedMapComputation` states the entire
arbitrary-resolution computation of `lem-sf-kinjective-derived-map-computation`.
Its five named theorems all have `sorry` as their whole proof. Four helper definitions
contain real categorical composites, and all belong to this node's canonical-map notion.
No new node, dependency repair, or statement correction is necessary. The existing
comparison `rightDerivedFunctorOfQuasiIsoResolutionsObjIso` is used without replacement.

Hypotheses and clauses, matched individually:

- Abelian categories A and B: `C : Type uC`, `D : Type uD`, independent
  `Category.{vC}` and `Category.{vD}` instances and `[Abelian C] [Abelian D]`.
- The additive functor: `(F : C ⥤ D) [F.Additive]`. No left exactness or preservation
  of quasi-isomorphisms is imposed: the dependency's additive clause alone is used.
- Homotopy and derived categories: `HomotopyCategory C (.up ℤ)` and `DerivedCategory C`,
  with independent `[HasDerivedCategory.{wC} C]` and `[HasDerivedCategory.{wD} D]`.
  `HomotopyCategory.quotient` expresses complexes modulo chain homotopy;
  `DerivedCategory.Qh` is Q on this category, and `DerivedCategory.Q` is Q on complexes.
- Enough K-injectives: `enough : ∀ K : CochainComplex C ℤ, ∃ I s,
  I.IsKInjective ∧ QuasiIso s`, with the full object and map types in the file.
  The `IsKInjective` definition is Mathlib's null-homotopy condition for maps from
  acyclic complexes. Resolution maps need not be monomorphisms.
- The pair (RF, eta): `F.rightDerivedFunctorOfQuasiIsoResolutions enough` and its unit,
  as supplied by `def-sfb-right-derived-functor`. Its canonical comparison
  `F.rightDerivedFunctorOfQuasiIsoResolutionsObjIso enough a` is precisely c_a:
  RF(Qa), followed by inverse eta_I, with the canonical quotient/localization
  presentation isomorphisms. Its type is an isomorphism, so the c_a invertibility
  clause is included with actual data.
- N, N', I, J are arbitrary `CochainComplex C ℤ`; the resolution hypotheses are
  `[I.IsKInjective] [J.IsKInjective] [QuasiIso a] [QuasiIso b]`.
  The map h is any `DerivedCategory.Q.obj N ⟶ DerivedCategory.Q.obj N'`.
- The unique homotopy class g: the first conjunct of `kInjectiveDerivedMapComputation`
  is `∃! g` in the Hom between the quotient objects of I and J, with
  `DerivedCategory.Qh.map g = kInjectiveResolutionHomTarget a b h`.
  The latter real-data helper is (in Lean's left-to-right order)
  `quotientCompQhIso.hom ≫ (Qa)⁻¹ ≫ h ≫ Qb ≫ quotientCompQhIso.inv`.
  The exterior isomorphisms only reconcile Qh(quotient I) with Q(I).
- The displayed computation: the second conjunct asserts, for every g satisfying
  precisely the preceding equation,
  `F.kInjectiveDerivedResolutionMap enough a b h = F.kInjectiveHomotopyImage g`.
  The left helper is c_a inverse, RF(h), c_b, and the right helper is Qh(F_K(g)),
  transported to Q(FI) and Q(FJ). `Functor.mapHomotopyCategory` is Mathlib's degreewise
  functor on homotopy classes and therefore gives exactly F applied to any chain-map
  representative; it does not choose an arbitrary map of complexes.
- Identity compatibility: the first two conjuncts of
  `kInjectiveDerivedMapComputation_functorial` assert that the identity homotopy class
  satisfies the transported identity equation and that its computed image is identity.
  Combined with the preceding uniqueness, this identifies the unique lift of identity.
- Composition compatibility: the third conjunct says that composable lifts g, g'
  satisfying their transport equations have `g ≫ g'` satisfying the equation for
  `h ≫ h'`. Uniqueness identifies it with that composite's lift. The final conjunct
  explicitly states preservation of composition of the computed images.
- For another resolution a', the canonical transition c_a inverse followed by c_a'
  is `kInjectiveDerivedResolutionTransition enough a a'`, defined as an Iso by
  composing the two recorded c isomorphisms. There is no chosen noncanonical transition.
- The unique k and Q(Fk) formula are both conjuncts of
  `kInjectiveDerivedResolutionTransition_computation`, with the transport equation
  specialized to h = identity. Quantifying the formula over every matching k,
  separately from `∃! k`, preserves uniqueness for the transport equation itself.
- Isomorphism, inverse, identity and three-resolution cocycle: the transition has
  type Iso; `kInjectiveDerivedResolutionTransition_laws` states its identity law,
  that its inverse is the reverse transition, and
  `T(a,b) ≪≫ T(b,d) = T(a,d)`.
- Intertwining for every h: `kInjectiveDerivedResolutionTransition_naturality`
  quantifies over a,a',b,b' and arbitrary h and states the square
  `M(a,b,h) ≫ T(b,b').hom = T(a,a').hom ≫ M(a',b',h)`.
  The map-computation theorem identifies each M with its Q(Fg), so this is the
  square specified by the final clause, without any restriction on h.

Dependency declarations read and used:

- `Mathlib.CategoryTheory.Abelian.Basic`: `CategoryTheory.Abelian`.
- `Mathlib.CategoryTheory.Preadditive.AdditiveFunctor`: `CategoryTheory.Functor.Additive`,
  the applicable clause of the Mathlib match for `def-sp-left-exact-additive`.
  I also read `Functor.rightDerived`, `InjectiveResolution.isoRightDerivedObj` and
  `Functor.rightDerived_map_eq` in `Mathlib.CategoryTheory.Abelian.RightDerived`,
  and the finite-limit/kernel preservation interfaces named in that match.
  Those ordinary higher derived functors are not the unbounded functor here.
- `Mathlib.Algebra.Homology.DerivedCategory.Basic`: `DerivedCategory`,
  `HasDerivedCategory`, `DerivedCategory.Q`, `DerivedCategory.Qh`,
  `DerivedCategory.quotientCompQhIso`.
- `Sheaf.CategoryTheory.RightDerivedFunctorOfQuasiIsoResolutions`:
  `CategoryTheory.Functor.rightDerivedFunctorOfQuasiIsoResolutions`, its Unit,
  its `_universal`, `_unique`, `Unit_isIso`, and `ObjIso` declarations were read;
  the functor and `ObjIso` are used directly. This public import also imports
  `Sheaf.CategoryTheory.KInjectiveTotalDerived` (proof dependency already carried
  by the defining node).
- `Mathlib.Algebra.Homology.DerivedCategory.KInjective`:
  `CochainComplex.IsKInjective.Qh_map_bijective`, the recorded Mathlib match of
  proof dependency `lem-weil-pbc-kinjective-hom-derived`; available transitively through
  the required public import. No extra imports are needed for the proof plan.
- `Mathlib.Algebra.Homology.HomotopyCategory`: `Functor.mapHomotopyCategory` and its
  representative formula, whose full signatures and construction were read.

Source check: read Stacks `derived.tex`, `lemma-K-injective-defined` (070Y) and
`lemma-enough-K-injectives-implies` (070K), including their proofs. The unit naturality,
Hom bijection, cancellation argument and seven-step node proof give the exact map
and coherence package; the node already identifies this as an agent formulation.
Each postponed theorem's docstring gives its corresponding part of this proof.

Edge cases checked mathematically before writing: zero complexes and the zero functor;
F = identity; a = identity on a K-injective complex; equal resolutions (identity
transition); opposite transitions (inverse); three unrelated resolutions (cocycle);
zero h; and a nonmonomorphic resolution of an acyclic complex into zero. Every formula
remains meaningful and has the stipulated behavior. All complexes are Z-indexed, with
no boundedness or termwise injectivity restriction. Source, target, morphism and
localization universes remain independent, with no added equality assumptions.

Searches for an existing full statement:

- `msearch.py ... leanfinder`, query “Compute an unbounded right derived functor on maps
  between arbitrary K-injective resolutions, compatible with change of resolutions”:
  eight hits on ordinary `rightDerived_map_eq`, higher right derived functors and
  injective resolutions of objects. None states this unbounded package.
- `msearch.py ... loogle`, query `"rightDerived", "map"`: four hits, namely two generic
  commShift naturality lemmas, a bounded-below unit instance and `rightDerived_map_eq`.
  None supplies this statement.
- `msearch.py ... leansearch`, query “Right derived functor computed on arbitrary
  K-injective resolutions and maps between them”: eight hits on ordinary derived
  functors, generic totalRightDerived and its universal property. No exact match.
- `msearch.py ... grep`, query
  `Qh_map_bijective|quotientCompQhIso|isIso.*Qh|mapHomotopyCategoryFactors`
  in `Algebra/Homology`: found the canonical localization, homotopy functor, and Hom
  bijection interfaces used here, not the full map computation/coherence package.
- `rg` on the same patterns in Mathlib's homotopy and derived-category directories
  confirmed those interfaces. Read their source signatures and docstrings.
- `rg` for the item id in `/home/ubuntu/weil-src-slopmaster2/WeilConjectures` and
  `lean/Sheaf`: no declarations carrying this node. Broader searches for
  `rightDerivedFunctorOfQuasiIsoResolutions|resolution.*[Mm]ap|[Mm]ap.*resolution`
  in their category-theory trees found the existing comparison used here and
  bounded-below or unrelated resolution-map results, not this full statement.

Validation: scompile.py compiled the single delivered module, both as a sandbox module
and at its intended library path, cleanly (1.5 and 1.6 seconds). An initial ambiguity
between `Functor.inv` and `CategoryTheory.inv` was repaired by qualifying the latter.
All variables/universes are explicitly bound, `autoImplicit` is false, every line
is at most 100 characters, and the node differs only in its `lean` record.
No statement dispute or node fault was found.

## Second reading by Q147

I performed a separate clause-by-clause rereading of the original node and final source;
no other agent was started, as the dispatch brief explicitly forbids that. The review
checked uniqueness of the homotopy-class equation separately from the image formula,
left-to-right composition order, the Qh/quotient-to-Q conjugations, and both paths of
the change-of-resolution square. The c_a object is the dependency's canonical comparison,
not an arbitrary Iso. It uses the arbitrary-quasi-isomorphism existence hypothesis, not
monomorphic resolutions. The image helper is Mathlib's quotient functor on homotopy
classes, so Fg is independent of representatives. All hypotheses and clauses are
accounted for in the correspondence above. No mathematical mismatch or further edit
was found in this rereading; the inverse-name qualification was the compilation repair.
The separate maintainer delivery review remains independent.
