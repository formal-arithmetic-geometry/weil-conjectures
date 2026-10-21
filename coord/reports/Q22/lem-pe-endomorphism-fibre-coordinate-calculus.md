## Worker report

Item: `lem-pe-endomorphism-fibre-coordinate-calculus`. Module:
`Sheaf.Algebra.Homology.EndomorphismFibreCoordinateCalculus`.
All eleven theorem declarations have proof `by sorry`; the four definitions have actual
specified data. No mathematical statement is corrected or disputed. This repair adds
`def-weil-signed-mapping-cocone-functor` with an `existing: true` record to own the
canonical signed mapping-cocone data already in the library. The item cites that
definition node instead of the theorem `lem-weil-signed-mapping-cocone-shift`.
The Lean module is byte-identical to the returned version at `876ef0d871f2`.

The source read was the Cones paragraph of
`literature/blueprint/main-20261015/blueprint/sec-proetale-coefficients/sk-lem-pe-derived-nakayama/sk-lem-pe-derived-nakayama-first-reduction.proof.md`.
I also read Stacks `derived.tex`, definition-cone (014E), and `homology.tex`,
definition-shift-cochain (011G). The former has cone differential `(du+sv,-dv)` before
reordering and shift, while the latter shifts differentials by `(-1)^r` and reindexes maps
without a sign. These give precisely this node's signs, including negative r.

Hypotheses and clauses, matched individually:

| Node text | Lean realization |
| --- | --- |
| Arbitrary abelian category A | Explicit universes `u v`, `{A : Type u} [Category.{v} A] [Abelian A]`; no equality between the universes. |
| Integer cochain complexes and chain maps | `CochainComplex A ℤ` and its category of chain maps. |
| Objects (V,s), with arbitrary chain endomorphism | `Endofunctor.Algebra (𝟭 (CochainComplex A ℤ))`, with `X.a` and `X.str`. No invertibility condition is imposed. |
| Intertwiners a satisfying as=ta | An algebra morphism `a : X ⟶ Y`, with underlying chain map `a.f`; its `a.h` says `a.f ≫ Y.str = X.str ≫ a.f`, exactly the same equation in Lean's left-to-right composition order. |
| Componentwise identities, composition, addition and zero | Existing Mathlib category of endofunctor algebras and `Endofunctor.algebraPreadditive` at the identity functor. The underlying operations are respectively identity, composition, sum, and zero of chain maps. |
| K(V,s)=Cone(s)[-1] | `endomorphismFibreFunctor.obj X` reduces to `mappingCocone X.str`, which is defined in Mathlib as `(mappingCone X.str)⟦(-1 : ℤ)⟧`. |
| Reordered degree-q biproduct V^q plus V^(q-1) | First conjunct of `endomorphismFibre_coordinates`: the actual map `biprod.lift (mappingCocone.fst X.str).f q ((mappingCocone.snd X.str).v q (q-1) ...)` is an isomorphism onto that ordered biproduct. This fixes the specified two projections, rather than asserting an unspecified degreewise isomorphism. |
| Differential (dv,-du-sv) | Last two conjuncts of `endomorphismFibre_coordinates` give the composites of `K.d q (q+1)` with its first and second projections: respectively `fst ≫ d` and `-(snd ≫ d) - fst ≫ s`. |
| K(a)(v,u)=(av,au) | `endomorphismFibre_map_coordinates` gives both projection equations for the actual map of `endomorphismFibreFunctor`; the second entry uses `a.f.f (q-1)` and the first uses `a.f.f q`. |
| Additive functor | The definition `endomorphismFibreFunctor` is the existing diagonal cocone functor specialized to the tautological endomorphism; `endomorphismFibre_additive` states its `Functor.Additive` property. Functor identities and composition are already part of the actual functor data. |
| Shift (V,s) to (V[r],s[r]) | Existing upstream `Endofunctor.Algebra.hasShift` at the identity functor. Its forgetful comparison is the identity; the structure morphism is the shifted endomorphism, with only that identity comparison composed on the left. `endomorphismPairTransformation_commShift` supplies the tautological compatible transformation's proof. |
| Specified natural chain isomorphisms sigma_r | `endomorphismFibreShift r` is a `NatIso` from shift-then-fibre to fibre-then-shift. Thus each component is a chain isomorphism, natural for every intertwiner, with its actual inverse. It is constructed from `SignedCoconeShift.coconeFunctorShiftNatIso`, using no arbitrary choice. |
| Formula (v,u) to (v,(-1)^r u) | First two conjuncts of `endomorphismFibreShift_coordinates` state the first and second inclusion formulas for the hom of that same natural isomorphism, using `r.negOnePow` and `shiftFunctorObjXIso` for the canonical degree reindexing. |
| Inverse given by the same formula | Last two conjuncts of `endomorphismFibreShift_coordinates` give the same coefficients, one and `r.negOnePow`, for the inv of that same natural isomorphism. |
| sigma_0 is identity under reindexing | First conjunct of `endomorphismFibreShift_coherence` is equality with `Functor.CommShift.isoZero`, which includes precisely the canonical zero-shift reindexings. |
| Successive shifts agree with r+r' | Second conjunct of `endomorphismFibreShift_coherence`, for all `r r' : ℤ`, is equality with `Functor.CommShift.isoAdd` of the two specified comparisons. This includes the canonical successive-shift identifications in both categories. |
| Every M and J with sJ=0 has the chain map eta_J | `endomorphismFibreAugmentation X J hJ`, with `{M : CochainComplex A ℤ}`, `(J : M ⟶ X.a)`, `(hJ : J ≫ X.str = 0)`, is the actual `mappingCocone.lift X.str J 0`. The named theorem `endomorphismFibreAugmentation_condition` supplies only its required chain-equation proof, with no unspecified data. |
| eta_J(m)=(Jm,0) | `endomorphismFibreAugmentation_coordinates` states both projection equations for this chain map. |
| Compatible a,J',g and tJ'=0 | `endomorphismFibreAugmentation_naturality` binds arbitrary pairs X,Y, arbitrary M,M', J,J', strict annihilation proofs hJ,hJ', an arbitrary chain map g, and `hsquare : J ≫ a.f = g ≫ J'`. |
| K(a) eta_J = eta_J' g | Conclusion of `endomorphismFibreAugmentation_naturality`: `eta_J ≫ K.map a = g ≫ eta_J'`, exactly the displayed identity with Lean's composition convention. |
| sigma_r eta_(J[r]) = eta_J[r] for every r | `endomorphismFibreAugmentation_shift` uses the very same `endomorphismFibreShift r`. Its left augmentation uses the named `endomorphismFibreAugmentation_shift_condition`, stating the shifted strict annihilation equation derived from hJ. Its right side is the shift of the original augmentation. |
| Identities of biproduct component morphisms | Every coordinate formula is a categorical composite in A, never an element calculation or a specialization to modules. |
| No boundedness or exactness hypotheses | None of the declarations assumes bounds, preservation of limits, exactness of a functor, vanishing of s, or invertibility of s. |

Dependency declarations inspected and used:

- `def-sp-abelian` is the Mathlib leaf `CategoryTheory.Abelian` in
  `Mathlib.CategoryTheory.Abelian.Basic`. I read its complete class signature and
  docstring (normal monos/epis, finite products, kernels, cokernels); its finite
  biproduct instances are available through the cone API.
- `def-weil-abstract-derived-category` is a Mathlib leaf. I read the recorded
  `DerivedCategory`, `HasDerivedCategory`, and `DerivedCategory.Q` interface in
  `Mathlib.Algebra.Homology.DerivedCategory.Basic`, and the complex/cone/shift
  interfaces that implement the portions used here. This item takes place at the
  level of complexes, so it requires no chosen localization or `HasDerivedCategory`
  hypothesis. The actual declarations used are `CochainComplex`, `mappingCone`,
  `mappingCocone`, `mappingCocone.fst`, `.snd`, `.inl`, `.inr`, `.lift`, and
  `shiftFunctorObjXIso`, in the Mathlib homological-complex, mapping-cone,
  mapping-cocone, and shift modules publicly imported by the signed-cocone module.
- The new definition dependency `def-weil-signed-mapping-cocone-functor` is recorded
  in `Sheaf.Algebra.Homology.SignedMappingCoconeShift`. I read the node and its whole
  module. The actual data reused are
  `CategoryTheory.SignedCoconeShift.coconeFunctor` and
  `CategoryTheory.SignedCoconeShift.coconeFunctorShiftNatIso`. The latter is built
  from `.signedCoconeShiftIso` with exactly the signed diagonal and canonical
  degree reindexing needed here. The general node omits the endomorphism-pair
  specialization, additive property, differential formulas, inverse coordinates,
  and strict augmentation clauses, so it does not already state this item.
- `Mathlib.CategoryTheory.Endofunctor.Algebra`: `Endofunctor.Algebra`, `.Hom`,
  `.Hom.h`, `.forget`, the category instance and componentwise operations.
- `Mathlib.CategoryTheory.Preadditive.EndoFunctor`:
  `Endofunctor.algebraPreadditive` specializes to the identity functor.
- `WeilConjectures.CategoryTheory.Endofunctor.Shift`: `Algebra.hasShift`, `.shift_a`,
  `.shift_str`, `.shift_map_f`, `.commShiftForget`, and its zero/add reindexings.

Edge cases checked against the coordinate computations: zero category/zero complex,
s=0, s=identity (allowed even though its fibre is contractible), J=0, the zero and
identity intertwiners, sums of arbitrary intertwiners, r=0, r=1, r=-1, arbitrary even
and odd negative r, successive shifts 1 then -1, and characteristic two. In all of
these the second differential coordinate remains -du-sv and the comparison uses
(-1)^r with square one. In characteristic two the signs coincide as required.
Nonzero differentials are allowed: the chain equation D squared = (0,ds-sd) uses
only that s commutes with d; it does not silently replace the complexes by graded
objects. For arbitrary test morphisms these are biproduct identities, so no concrete
category or elements are assumed.

Searches made, all through the prescribed tools or read-only rg:

- `msearch.py ... leanfinder "The homotopy fibre of a chain endomorphism is additive
  with coherent signed integer shifts and strict kernel augmentations"`: eight
  hits, including `HomologicalComplex.homotopyCofiber`, its homotopy data, and
  `CochainComplex.instHasHomotopyCofiberOfHasBinaryBiproductXHAddOfNat`. None states
  the complete node.
- `msearch.py ... loogle "CategoryTheory.End, CochainComplex.mappingCocone"`: no hits.
- `msearch.py ... grep "mappingCocone|endomorphism"
  Algebra/Homology/HomotopyCategory`: five mapping-cocone hits, including its
  definition and first projection. Read the complete MappingCocone source and the
  cone/shift signatures and formulas needed above.
- `msearch.py ... leansearch "Category of pairs consisting of an object and an
  endomorphism with intertwining morphisms"`: eight hits; generic endomorphisms,
  Karoubi-envelope objects and bicategorical endomorphisms, no full item match.
- `msearch.py ... loogle "CategoryTheory.Endofunctor.Algebra"`: twelve hits; inspected
  the category of endofunctor algebras and its full morphism signature and docstrings.
  At the identity functor this is exactly the needed pair category, so no new
  definition of pairs or intertwiners was introduced.
- `rg` in `lean/WeilConjectures` for the item id returned no declarations. Searches
  for `endomorphismFibre|endomorphismFiber|EndomorphismFibre|EndomorphismFiber` in
  `lean/WeilConjectures`, `lean/Sheaf`, and `dag/lean_names_upstream.json` returned no
  existing names. Further searches for `mappingCocone` and `CommShift` found the
  existing signed-cocone and Roos modules; their maps were read rather than copied.
- Searches of Mathlib/project sources for endomorphism categories and shifts found
  `Mathlib.CategoryTheory.Preadditive.EndoFunctor` and upstream
  `WeilConjectures.CategoryTheory.Endofunctor.Shift`. Both are reused directly.
- DAG search for `signed-mapping-cocone-shift` found the recorded theorem node.
  The H2 return requires a separate definition node owning its existing construction
  data; this repair adds that record and duplicates no Lean definition.

Validation: `scompile.py Q22 lem-pe-endomorphism-fibre-coordinate-calculus <module>`
passed with no diagnostics, both in sandbox form (16.7 s) and at its actual library
module path (15.7 s), under the unchanged 60-second per-file limit. The first compile
identified an unqualified `shiftFunctor` resolving to the cochain-specific definition;
qualifying it as `CategoryTheory.shiftFunctor` fixed that elaboration error. All
universes and variables are explicitly bound. All Lean lines are at most 100 characters.

## Second reading by Q22

This is the worker's final consistency check, not a claim of an independent second
agent review. The dispatcher brief prohibits starting other agents and assigns the
independent review to the maintainer reading the delivery.

With the node and complete module open, I checked every row of the correspondence
above. The first coordinates are degree q and the second are degree q-1, including
q-1+r in the signed comparison; both the forward and inverse comparison have the
same sign on the second inclusion. Both coherence laws and the augmentation-shift
equation refer to `endomorphismFibreShift`, so no different choice of comparisons
can enter the last clause. The map `endomorphismFibreAugmentation` has specified J
and zero cochain data; only its chain-equation proof is postponed. Naturality binds
both annihilation equations and the required commuting square. I found no dropped
hypothesis, added assumption, missing clause, universe restriction, hollow definition,
or mathematical discrepancy. The only correction during elaboration was the
`CategoryTheory.shiftFunctor` qualification noted above.


## New nodes

`def-weil-signed-mapping-cocone-functor` is a definition node in the item's chapter
and unit with an `existing: true` record on
`Sheaf.Algebra.Homology.SignedMappingCoconeShift`. It owns exactly:

- `CategoryTheory.SignedCoconeShift.coconeMap`: the shift by -1 of the canonical
  diagonal cone map of a commuting square.
- `CategoryTheory.SignedCoconeShift.coconeFunctor`: for arbitrary S, F, G and τ,
  the actual objectwise mapping-cocone functor using the preceding square map.
- `CategoryTheory.SignedCoconeShift.signedCoconeShiftIso`: for arbitrary integer m,
  the scalar `m.negOnePow` times the shifted inverse cone comparison followed by
  the canonical interchange of shifts.
- `CategoryTheory.SignedCoconeShift.coconeFunctorShiftIso`: the object comparison
  induced by the shift-compatible square for F, G and τ, followed by that signed iso.
- `CategoryTheory.SignedCoconeShift.coconeFunctorShiftNatIso`: those same components
  assembled into a natural isomorphism. It assumes the existing coherent shifts on
  F and G and compatibility of τ, without asserting a new coherence theorem.

The node explicitly binds arbitrary categories, complexes, squares, functors, natural
transformations, and integer shifts. Its two definition dependencies provide the
abelian-category and cone/shift conventions. The main record's signature is verbatim
`def coconeFunctor : S ⥤ CochainComplex A ℤ`, under the source module's explicitly
bound universes a, b, s, v and its category/abelian assumptions. There is no new
module, no new definition data and no postponed theorem for this node.

Repair searches on 2026-10-21, recorded in the new node:

- LeanSearch, “The functorial mapping cocone of a natural transformation between
  functors to cochain complexes with its signed shift natural isomorphism”: eight
  hits, including `mappingCone.shiftIso` and `Functor.mapCochainComplexShiftIso`;
  none supplies the complete functor interface.
- Loogle, `"mappingCocone", "shift"`: zero hits.
- Mathlib grep, `coconeFunctor|signedCoconeShiftIso|def mappingCocone` in
  Algebra/Homology: one hit, the definition of `mappingCocone` at line 33.
- Read-only rg across dag/nodes, lean/WeilConjectures and lean/Sheaf found the
  existing theorem node and its implementation, and consumers in RoosCommShift.
  No definition node owns the constructions; no upstream WeilConjectures match.
- `blueprint_refs.py search "signed mapping cocone"`: zero blueprint nodes.
  `blueprint_refs.py ancestor` confirms `det-pe-derived-nakayama-first-reduction`.

## Returned point H2 repaired

The independent review of immutable head `876ef0d871f2` found that this item's
statement dependencies named the theorem `lem-weil-signed-mapping-cocone-shift`,
although the item only uses plain definitions from its module, not `.choose` or
its conclusion `coconeCommShift`. The repair adds the definition ownership node
above and substitutes it in the item's statement dependencies. The mathematical
statement, proof plan, proof dependencies and Lean module are unchanged. Comparing
the saved item with current shared main found only the expected `lean` and
`stmt_deps` differences before repair; all other base fields are retained.

I reread the complete signed-cocone source and the item's module. The two calls
are exactly `coconeFunctor` in `endomorphismFibreFunctor` and
`coconeFunctorShiftNatIso` in `endomorphismFibreShift`. The new node owns both and
all three intervening data constructions requested by the maintainer. No theorem
conclusion is substituted for definition data. Zero complexes, zero maps, zero and
negative shifts and distinct object/morphism universes remain covered, as in the
original clause-by-clause reading above. No Lean change is necessary.

Repair validation: the prescribed `scompile.py` passed cleanly (sandbox 16.7 s,
library path 15.7 s). The repaired packet passed `deliver2.py --no-push`: commit
`d0277a2fe17`, including the new existing-definition node, passed server preflight
and all per-file compiler checks. The final self-check confirms only `lean` and
`stmt_deps` differ from the base item and all five requested data declarations are
owned by the new node.
