## Worker report

The module `Sheaf.Paper.NativeGeometricBrownConstructibleComparison` states
`WeilConjectures.NativeGeometricBrown.native_geometric_brown_constructible_comparison`.
It uses the actual native internal-module derived categories. All theorem proofs are
`sorry`; all definitions contain actual data. `preserves_constructible` is the first
assertion of this same node (its proof step 1), extracted solely to define the restriction.
It is listed with the main theorem in lean.declarations and has its own source/proof docstring.

Hypothesis and clause correspondence, checked against the whole node:

- The finite field is `(k₀ : Type u) [Field k₀] [Finite k₀]`, and the native framework's
  fixed `AlgebraicClosure k₀` is the algebraic closure k. This is the same choice already
  used by ProEtaleWeilSheaf and the recorded native framework, with no new model of k.
  The prime and characteristic condition are `(l : ℕ) [Fact l.Prime]` and
  `[Fact (ringChar k₀ ≠ l)]`. Omega is exactly `PadicAlgCl l`.
- `X₀`, `Y₀`, their `Over (Spec (.of k₀))` structures, finite-type structure hypotheses
  (`LocallyOfFiniteType` and `QuasiCompact`), target `QuasiSeparated`, and the relative
  morphism's `IsOver`, `IsSeparated`, `LocallyOfFiniteType`, and `QuasiCompact` are all
  explicit section binders used by the theorem. No absolute separatedness is imposed.
- The compactification is literally `nativeWeilChosenCompactification k₀ f₀`, which
  unfolds to `HasCompactification.compactification` with the native Nagata witness.
  `nativeWeilUnderlyingCompactSupport` uses its two geometric-fiber maps and is
  `D(j_!)` followed by the total derived native proper image. No arbitrary ambient
  functor is substituted. The dependency's existing definition supplies its middle
  scheme and coefficient maps. The native heart and Frobenius lifts, F_W, induction,
  forgetting and its unit are background constructions of the stated framework and
  free-resolution dependencies; this node asserts no extra equivariant property.
- C_T is exactly `(ProEtale.DerivedCategory.boundedAdicConstructible l T).FullSubcategory`.
  This is bounded ordinary derived cohomology with the original locally stratified,
  locally finite-free native coefficient models (varying finite ranks included).
  L_T is the existing `nativeWeilUnderlyingHull` = the existing `localizingClosure`
  of that very predicate. `inclusion` is Mathlib's `ObjectProperty.ιOfLE` for
  `le_localizingClosure`. The single scheme universe u fixes derived Homs, localizing
  coproducts and the small representatives consistently; the native Hom universe is u+1.
- RX and RY are precisely the dependency's `Realization` records. Their `.J` has the
  common finite-field pair category, not a single finite field, as its domain.
  `realizationFunctor` only restricts that `.J` to its full constructible image;
  `realizationEquivalence` constructs its inverse using the recorded fully faithful
  and image properties. It makes no choice from a bare sorry existence theorem.
- `Fs`, `Gs`, `stageAdj` bind the fixed stage functors and adjunction in the node's
  second paragraph; `alpha` binds its supplied scalar-extension comparison with the
  actual native F. They are parameters for the already chosen adjunction/comparison,
  not a claim that an ambient pro-etale adjunction exists. They may in particular be
  instantiated by the coefficient-adjunction and compact-support-realization records.
- `constructibleRight RX RY Gs` is definitionally J_Y inverse then Gs then J_X,
  hence exactly the displayed G_c. `constructibleLeft` is the full restriction of F,
  with `preserves_constructible` giving its original image assertion.
- The outer `∃ adj` says F restricted to C_X is left adjoint to this G_c. Its first
  conjunct specifies the Hom bijection on every `J_X K`: precompose by `alpha.hom`,
  postcompose by the inverse realization counit e_Y, use `Equiv.ofBijective` for
  full faithfulness of J_Y, apply `stageAdj.homEquiv`, and apply `RX.J.map`.
  Naturality of `Adjunction.homEquiv` extends the formula to every A by essential
  surjectivity of J_X, exactly as the node's proof step 1 specifies.
- The next conjunct is the counit at every M, on underlying ordinary derived arrows:
  `alpha.inv.app (Gs.obj (JY.inverse.obj M))`, then `RY.J.map stageAdj.counit`,
  then the chosen `JY.counitIso.hom`. Lean composition reads left to right, matching
  the displayed sequence of three arrows in the node.
- The `∀ hL G ambientAdj` part quantifies over every adjunction for the restriction
  of this same actual F to the existing localizing hulls. hL is its codomain
  membership witness, not a new existence premise on an unrelated functor.
- `∃ t : constructibleRight ... ⋙ inclusion ... ≅ inclusion ... ⋙ G` is the
  natural isomorphism in L_X. The first conjunct fixes each `t.hom.app M` as the
  ambient Hom transpose of the constructible counit. The following conjunct says
  that G of each constructible input has bounded native constructible cohomology.
- The next conjunct quantifies over every constructible M, A, every `n : ℤ`, and
  every `a : A⟦n⟧ ⟶ G_c M`. Its equation is postcomposition with t equal to the
  inverse constructible adjunction followed by the ambient adjunction. Both full
  inclusions retain the original ordinary derived arrows.
- The last conjunct quantifies over every distinguished triangle with first map t_M,
  every B in L_X, every integer n, and every map `B⟦n⟧ ⟶ Q`, asserting that map is
  zero. Every ambient cone is in L_X by triangulation and repleteness of the hull,
  so writing the triangle in this full subcategory excludes no cones in the node.

Dependency declarations used:

- `WeilConjectures.WeilSheaf.LowerShriek`: native `ProEtale.AdicSheaf`,
  `ProEtaleWeilSheaf`, geometric fibers, actual operations, chosen compactification.
- `Sheaf.CategoryTheory.FreeDerivedWeilResolution`: recorded exact free derived
  adjunction and cyclic resolution; background to the native framework.
- `Sheaf.Paper.LocallyFiniteAdicConstructibleRealization`:
  `LocallyFiniteAdicRealization.Realization`, `.J`, `.fully_faithful`, `.image`.
- `Sheaf.Paper.LocallyFiniteAdicCompactSupportRealization`:
  `LocallyFiniteAdicCompactSupport.CompactSupportComparison.alpha` and `.preserves`
  give the chosen alpha and preservation that the statement transports.
- `Sheaf.Paper.ConstructibleExceptionalAdjunctionCoefficients`:
  `ConstructibleExceptionalCoefficients.Operation.adjunction` (closed coefficient
  stage) and `exists_system` supply the already fixed stage adjunction.
- New definition dependency `def-sf-native-geometric-localizing-data` re-exports
  the existing abbreviations from module `Sheaf.Paper.NativeWeilLocalizingBrownAdjoints`, solely to reuse
  `AlgebraicGeometry.nativeWeilUnderlyingHull`, `nativeWeilUnderlyingCompactSupport`
  and `nativeWeilChosenCompactification`. These definitions were read in full. No
  Brown existence conclusion is assumed by the comparison theorem.
- Mathlib `ObjectProperty.IsTriangulated`, `lift`, `liftFullSubcategory`, `ιOfLE`,
  `Functor.asEquivalence`, `Equiv.ofBijective`, and the ordinary `Adjunction` API.
  The size convention is implemented by explicit u, not a fictitious object.
- Proof imports: `Sheaf.CategoryTheory.LocalizingHomTest` and its
  `ObjectProperty.isIso_of_bijective_postcomp_shift_generators`;
  Mathlib `Adjunction.mkOfHomEquiv` (already in the public Basic import),
  `Pretriangulated.Triangle.isZero₃_iff_isIso₁` (Pretriangulated import).

Edge cases checked before writing: empty source and target give the zero categories
and zero-map statements; rank zero and rank varying between covering members remain
in the original constructible predicate; n includes zero and negative integers;
identity compactification and identity coefficient-field transition impose no extra
restriction. No compactness or smallness of the entire constructible class is assumed.
The cone assertion uses any distinguished cone, not a chosen noncanonical cone.

Searches (2026-10-24 UTC):

- msearch.py leanfinder: "Transport a constructible adjunction through equivalences
  and compare its right adjoint with the Brown right adjoint on the localizing
  closure". Eight hits, including `Adjunction.localization`, condensed free/forget
  adjunctions and sheaf adjunctions; no native constructible/Brown comparison.
- msearch.py loogle: `CategoryTheory.Adjunction, CategoryTheory.Equivalence`.
  Six hits, including `Equivalence.toAdjunction`, its dual and
  `Equivalence.trans_toAdjunction`; no whole statement match.
- msearch.py grep: `rightAdjointUniq|restrictFullyFaithful|ofNatIsoLeft` in
  CategoryTheory. Twenty-five hits: useful ordinary adjunction API only.
- rg of Mathlib's full-subcategory, equivalence, fully faithful and triangulated
  APIs identified existing lift/inclusion/closure constructions; they are reused.
- rg `brown.*[Cc]ompar|geometric.*[Bb]rown|constructible.*[Bb]rown` in
  lean/WeilConjectures and lean/Sheaf found integral/restriction comparisons but
  none about this native realization. `rg` for the exact node id in
  lean/WeilConjectures returned no match. Additional native/hull searches found
  the landed helper module now cited instead of duplicated.

No statement correction, dependency-module repair, or disputed statement. The new
definition node described below replaces the unneeded theorem statement dependency.
No mathematical clause or Lean signature has been changed.

Validation: scompile.py compiled the complete delivered module in sandbox mode and
at its final module name, with no errors or warnings. Compiler-driven repairs were
explicit full-subcategory morphism endpoints, `Pretriangulated.Triangle.mk` and
exposing the inherited constructible triangulation. No universe was equated or reduced.

## Second reading by NL

The dispatcher expressly prohibits starting another agent and assigns independent
review to the maintainer. This section is a separate self-reading, not a claim of an
independent second worker. I reopened the node, each dependency interface and the final
file. The hypothesis/clause mapping above records that reading in full. I checked the
orientation of alpha (stage then J_Y to J_X then F), so its inverse occurs first in the
counit. I checked that the stage Hom transport uses e_Y inverse, while the counit uses
e_Y, and that the comparison t is the ambient transpose of that same counit. I checked
that the generator-Hom formula uses every integer shift and that cone vanishing is
for every B in the localizing hull, not merely constructible B. The only added
statement dependency is now the definition node re-exporting the already landed native
helper definitions. The Brown-existence theorem is absent from stmt_deps. The Lean
import remains the module containing those definitions, and no declaration of the
comparison module invokes its Brown theorem.


## Repair of returned delivery

Returned head: `2fcd36887fb2`. The sole numbered finding was H2: the old eighth
statement dependency was the Brown-existence theorem although only its three plain
abbreviations were used. I compared the retained node with the current shared base:
the base has seven dependencies and no Lean record. I restored those seven unchanged
and added `def-sf-native-geometric-localizing-data` instead. This implements the
maintainer's explicitly permitted `existing: true` re-export option. The original
comparison module and its mathematical signature are unchanged; the import is needed
for the existing definitions, while G and ambientAdj remain universally quantified.
The advisory about Fs, Gs, stageAdj and alpha requires no correction.

## New nodes

`def-sf-native-geometric-localizing-data` records exactly the three existing
real-data definitions in `Sheaf.Paper.NativeWeilLocalizingBrownAdjoints`, using
`existing: true`, so it adds no duplicate Lean module or declaration. Its source is
the native geometric setup serving the final exceptional-adjunction sentence of
`cor-coef-verdier-weil-equivariance.proof.md`. The DAG search found these names only
as auxiliary declarations of the Brown theorem node, not a definition node for this
interface; the return explicitly requests this separation. `blueprint_refs.py search
native-geometric-localizing` found no match. LeanSearch and LeanFinder each gave
eight unrelated topological/quasi-compactness hits; Loogle did not know the project
localizingClosure name; Mathlib CategoryTheory grep gave zero hits for the native
helper names/closure query. Project rg found the exact three existing abbreviations,
which are used, not redefined. Raw search results, dates and verdicts are recorded
in the new node's mathlib_searches.

Clause correspondence for the definition node: `nativeWeilUnderlyingHull` is
literally `boundedAdicConstructible.localizingClosure` in the fixed native geometric
fiber; its existing closure quantifies over all replete triangulated properties
closed under Hom-universe coproducts. `nativeWeilUnderlyingCompactSupport` takes any
actual `Compactification f`, installs `Compactification.over`, and composes the
geometric-fiber open extension-by-zero `mapDerivedCategory` with native proper
image `rightDerivedFunctor`, using the original coefficient maps.
`nativeWeilChosenCompactification` has precisely field, qc+qs target and separated
finite-type map hypotheses and is exactly the native Nagata choice with its specified
existence witness. These definitions assert no preservation or adjoint existence.
The zero/empty scheme, arbitrary compactification, rank-zero and all integer-shift
cases remain available. The new node cites the native-framework, size,
triangulated-subcategory and compactification definitions only.
