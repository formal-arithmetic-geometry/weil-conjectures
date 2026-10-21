## Worker report

The item is stated in `Sheaf.Algebra.Homology.FiniteFreeCompletionExchange`, declaration
`CategoryTheory.PrincipalQuotientCompletion.finiteFreeCompletionExchange`. Its only
postponed proof is `sorry`. The accompanying definition module
`Sheaf.Algebra.Homology.PrincipalQuotientCompletionModel` constructs the ordinary
quotient-tower/Roos functors and defines the universal completion model with its unit.
All definition data are real constructions or structure fields; no data are chosen
from an existence theorem. The original item statement and proof are unchanged.

Hypothesis-by-hypothesis and clause-by-clause correspondence:

- The site is `{C : Type u} [Category.{v} C]` with `J : GrothendieckTopology C`.
  `[EssentiallySmall.{r} C]` expresses precisely smallness in the module universe.
  The sheaf-compose, sheafification and locally-bijective-equivalence instances are
  the existing module-sheaf presentation requirements; they impose no geometric
  condition. Coefficient universe `r` is independent of both site universes.
- `R S : Sheaf J CommRingCat.{r}` and `φ : R ⟶ S` are the ring sheaves and their map.
  `ringedSiteModules` is the recorded Mathlib module-sheaf specialization.
- `_hfree` asserts existence of `d : ℕ` and an isomorphism of the restricted regular
  S-module with the coproduct of `Fin d` copies of the regular R-module. This is
  global finite freeness, including rank zero; the statement chooses no basis.
- `t` and `vS` are global sections of the unit modules over R and S. `_ht` and `_hv`
  say their multiplication maps are monomorphisms, i.e. sheafwise injective.
- `uS` is the global unit section; `_hu` asserts invertibility in every section ring.
  Its inverses automatically respect restrictions by uniqueness of inverses, so this
  is invertibility as a global section even if the site has no terminal object.
  `_he : 1 ≤ e` and `_hrelation` express `φ(t)=uS*vS^e` on every object.
- The three `HasExactLimitsOfShape (Discrete ℕ)` hypotheses say countable products
  are exact in R-modules, S-modules and abelian sheaves, respectively.
- `DerivedCategory` is the ordinary unbounded category of ℤ-indexed cochain complexes;
  `wR` and `wS` independently select its two localization universes.
  `F : DerivedChangeOfRingsCochainModel φ` is the recorded canonical ordinary and
  derived extension with counit, not an unconstrained functor.
- `CR : Model R t` and `CS : Model S vS` are universally characterized quotient
  completions. `quotientTower` is the existing tower of sheaf cokernels tensored with
  the representative; its natural indexing `n : ℕ` denotes positive level `n+1`.
  The existing construction puts the quotient on the left of the tensor; the
  principal-tower dependency explicitly identifies this with the symmetric model.
- `Model.completion`, `counit`, `universal` and `computes` identify that completion
  on every K-flat representative with the actual shifted Roos cone of its quotient
  tower. Exact products identify this cone with the recorded strict derived limit.
  `Model.unit`, `augmentation`, `coordinates` and `unit_computes` fix precisely the
  quotient augmentation: zero shifted-product coordinate, product of quotient maps.
- `ε : CR.completion ⋙ F.T ≅ F.T ⋙ CS.completion` is the natural isomorphism
  `T C_R ≅ C_S T`. The first conjunct is, for every derived object Q, the equation
  `F.T.map (CR.unit.app Q) ≫ ε.hom.app Q = CS.unit.app (F.T.obj Q)`.
- The second conjunct is the specified-map clause on every K-flat representative.
  The subtype value `roos.β` in `RepresentativeComparison` is an isomorphism of
  strict finite-stage towers. Its first predicate conjunct pins it by the canonical
  quotient maps. These are degreewise
  epimorphisms (a quotient tensored with any module is a quotient), and remain so
  under finite-free extension. Thus the equation uniquely pins the balanced formula
  `(rbar⊗p)⊗s ↦ φ(r)bar⊗(p⊗s)`; it introduces no arbitrary quotient identification.
- `product_formula` pins the canonical product comparison `c` by all its projections.
  `cone_formula` and the real generic definition `scalarRoosCoordinates` specify
  both actual additive cone coordinates of `δ`, using c in
  degrees p and p+1, including the signed cone convention of `roosχ`.
- `arithmetic_formula` specifies the existing `block` map on the first (shifted)
  coordinate and `selection` on the second coordinate of `a`; `arithmetic_quasiIso`
  makes its localized map invertible. The index is `e*(n+1)-1`, so positive level
  n+1 goes exactly to e(n+1), with no zero-level quotient substituted.
- `RepresentativeRoosComparison` states the product and cone formulas generically
  before specializing to the quotient towers, avoiding repeated unfolding of total
  tensor constructions during elaboration. The second predicate conjunct in `RepresentativeComparison` says
  that ε followed by the target K-flat counit, normalized completion
  comparison and arithmetic map equals the source normalized comparison followed
  by δ. It therefore specifies exactly inverse arithmetic restriction after the
  tensor/product and quotient comparison. It does not choose an arbitrary inverse.
- No basis appears in the specified maps: each is pinned by quotient maps, product
  projections or the fixed arithmetic coordinates. Hence the resulting exchange is
  basis independent. All representatives are ℤ-indexed, with no boundedness,
  completeness or finite-cohomological-dimension predicate.

Recorded statement dependency declarations read and used:

- `Sheaf.CategoryTheory.SiteCoveringAxioms`:
  `CategoryTheory.Precoverage.IsSiteForCoverings`; the site is used through its
  Grothendieck topology and Mathlib's sheaf category, as in its docstring.
- `Sheaf.CategoryTheory.RingedSiteModules`: `CategoryTheory.ringedSiteModules`.
- `Mathlib.Algebra.Homology.DerivedCategory.Basic`: `DerivedCategory`,
  `HasDerivedCategory` and the localization `DerivedCategory.Q`.
- `Sheaf.Algebra.Homology.DerivedChangeOfRingsCochainModel`:
  `SheafOfModules.DerivedChangeOfRingsCochainModel`, supplied by
  `nonempty_derivedChangeOfRingsCochainModel`; its `E`, `T`, `ε` fields are used.
- `Sheaf.Algebra.Homology.KFlatIndependentCoefficients`:
  `CochainComplex.IsKFlatIndependentCoefficients`.
- `Mathlib.Algebra.Homology.BifunctorShift`: `CochainComplex.mapBifunctor` and
  `map₂CochainComplex`, using the same recorded sheaf tensor.
- `Sheaf.CategoryTheory.RingedStrictTowerHomotopyLimitIndependentCoefficients`:
  `CategoryTheory.ringedStrictTowerHomotopyLimitIndependentCoefficients`.
- `Sheaf.CategoryTheory.StrictTowerArithmeticRestriction`:
  `CategoryTheory.StrictTowerArithmetic.strictTowerArithmeticRestriction`, with
  its publicly re-exported `index`, `complexRestriction`, `selection` and `block`.
- `Sheaf.CategoryTheory.StrictRoosComparison`: `CategoryTheory.strictRoosComparison`.
  These last three theorem modules provide the proof plan. The explicit actual-cone
  interface uses their existing general categorical constructions and never forces
  the site and coefficient universes to coincide merely to instantiate a specialized
  theorem signature.

The helper additionally uses the recorded `def-pur-principal-koszul-quotient-towers`
module `Sheaf.Algebra.Homology.PrincipalKoszulQuotientTowers`:
`principalReductionTower`, `koszulTowerComplex`, `koszulTowerComplexMap`,
`globalSectionMultiplication`, `reductionTensorTower`, `koszulRepresentativeQuotient`;
and `def-weil-strict-roos-model`, module `Sheaf.CategoryTheory.StrictRoosModel`:
`roosF`, `roosP`, `roosχ`. The ordinary quotient functor is built from the recorded
curried tensor, `map₂CochainComplex`, precomposition by `principalReductionTower`,
and the existing degreewise transposition. No quotient, tensor or cone is redefined.
The model uses Mathlib's `Functor.IsLeftDerivedFunctor` directly for its universal
condition; its counit is invertible on precisely the recorded K-flat complexes.

The theorem docstring records all nine proof steps, including finite-free scalar
coordinates, K-flat resolution/change of rings, the balanced quotient calculation,
additive Roos comparison, arithmetic restriction, the unit equation on both
coordinates, representative invariance, localization descent and basis independence.
Available recorded proof-dependency modules are imported without public re-export.

Edge cases checked mathematically: `d=0` makes the S-module category zero; `e=1`
gives identity selection and single-term blocks; a unit t or vS makes the corresponding
quotients zero; the zero complex and the empty site cause no exception; complexes may
be unbounded in both directions. No nonzero-ring assumption is added. Monomorphism
of multiplication agrees with the stipulated non-zero-divisor condition in the zero
ring as well. A finite basis is used only to verify invertibility, never to define ε.

Searches for an existing item statement: `msearch.py` LeanFinder query
“Finite free change of rings commutes with quotient derived completion of arbitrary
unbounded complexes of module sheaves” returned ordinary `IsAdicComplete` and
`AdicCompletion` results, not a sheaf/unbounded completion comparison. Loogle
`"AdicCompletion", "ofTensorProduct"` returned ordinary module completion maps and
finite Noetherian equivalences, with different hypotheses and no strict quotient unit.
Mathlib grep `completion.*tensor|tensor.*completion` under Algebra found no match.
Project grep for `PrincipalQuotientCompletion`, `quotientRoos`,
`finiteFreeCompletionExchange` and the item id in WeilConjectures, Sheaf and the
upstream name map found no existing declaration. Searches are retained in
`searches.jsonl`; helper searches are also recorded in its new node.

## New nodes

`def-pur-principal-quotient-completion-model` packages the universal quotient-Roos
completion and its normalized unit over an arbitrary ring sheaf, using existing
quotient towers, K-flatness, derived categories and the strict Roos construction.
Its source is Stacks 06YS/06YT for K-flat computation and 0941 for strict derived
limit, as combined explicitly in the item's DAG proof. This is definition data;
existence is asserted by the item, not hidden in the definition. LeanSearch for
“Total derived principal quotient completion functor on sheaves of modules as a left
derived Roos quotient tower with canonical unit” returned generic derived functors,
unit modules and sheafification. Loogle `"IsLeftDerivedFunctor"` returned the generic
universal property, not the completion model. LeanFinder for the quotient-Roos/unit
model returned presentation, sheafification and free-module results. Mathlib grep
`quotientRoos|QuotientCompletion|completion.*Roos` found only two unrelated uniform
space completion occurrences. Direct project/name-map grep found no declarations.
DAG searches found related finite-free completion lemmas and scheme-specific
comparison data, none defining this arbitrary-ring-sheaf model; blueprint search
“quotient completion” found zero nodes. The nearest blueprint ancestor is
`def-weil-derived-pullback-tensor-hom`, main-20261015, final paragraph on integral
coefficient derived inverse limits. The new node and the item retain that route.

## Second reading by ND

The dispatcher explicitly prohibits starting other agents. This is a second reading
by the same worker; the maintainer performs the independent review after delivery.
With the original item, both modules, the new definition node, Stacks 06YS/06YT/0941
and the blueprint ancestor open, I rechecked each correspondence above. In particular:
finite freeness is global and existential, not locally free with arbitrary rank;
regularity is stated on each respective ring, the unit relation is objectwise but
natural, and all three exact-product hypotheses remain. The target subsequence is
`e*(n+1)-1` in the zero-based encoding. The cone formulas put block summation in the
shifted coordinate and selection in the ordinary coordinate; the quotient unit is
`(0,q)`. ε is a natural isomorphism on derived categories and its equation uses those
same units. Its representative equation includes both cochain counits, so no arbitrary
identification with a derived tensor or completion is substituted. The new model's
universal property determines its functor and counit up to unique compatible
isomorphism, while its coordinates determine its augmentation and hence the unit.
The helper defines no new sheaf tensor, quotient tower, K-flat predicate or Roos cone.
The review found no mathematical statement correction necessary.

## Validation

The required initial dry run found the prior attempt's absent item node record.
Both node records have now been supplied. Early compilation hit a missing published
`WeilConjectures.Mathlib.LinearAlgebra.TensorProduct.Basic.olean`, including server
confirmation. An explicit import of this existing dependency made it available to
the wrapper's private compilation. No live source, build artifact, launcher tool or
Git state was edited directly; all compiles use `scompile.py` under its 60-second limit.
The quotient model compiled successfully. Main-file diagnostics about noncomputability
and inferred restriction categories were repaired. Final compile and delivery results
are appended below.

Final two-module `scompile.py` completed successfully with no errors or warnings.
The helper compiled in 46.4 seconds (49.7 seconds for its sandbox check); the item
compiled in 23.9 seconds (24.1 seconds for its sandbox check). All used the default
heartbeat setting and the prescribed 60-second per-file wall-clock limit. The large
concrete structure was refactored into generic `RepresentativeRoosComparison` data
plus the quotient specialization, rather than increasing either compile limit.

## Repair of returned delivery 55cd6f9a897b

The initial prescribed dry run reproduced the return: the private helper overlay
and sandbox checks reached the 60-second limit, and confirmation against current
server sources also timed out. The live item node still has no Lean attachment;
comparison with the saved packet shows changes only in `lean` and the added
statement dependency on the new model node. The returned source was retained.

A temporary Lean profiler trace showed that `transpose` and `quotientTower`
elaborated quickly, while generated `Model` recursors, no-confusion declarations
and injectivity lemmas repeatedly checked the concrete quotient total-tensor
identification in the coordinate field. Matching the transparency settings already
used by the imported Roos module alone did not resolve the timeout.

The repair names the canonical map `quotientProduct R t P`, with its explicit
codomain `roosP ((quotientTower R t).obj P)`, as the actual existing
`Pi.lift (koszulRepresentativeQuotient R P t)`. `Model.coordinates` uses this map.
This moves the concrete identification into a single definition check and leaves
the model's generated declarations with a shared, explicitly typed term. No map
is chosen or postulated: unfolding the new definition gives the old coordinate
formula verbatim. Its source/blueprint docstring and `lean.declarations` entry
are included. Temporary profiler settings were removed; the file and heartbeat
limits were not increased.

The same worker reread the item, both modules, the new node, the recorded K-flat
and change-of-rings signatures, the principal quotient maps, Stacks 06YS/06YT/0941,
and the main-20261015 blueprint ancestor's final paragraph. All hypothesis and
clause correspondences in the original report remain unchanged. In particular the
new name does not change the `(0,q)` unit, positive quotient indexing, arithmetic
selection/block formulas, independent universes, or the unbounded scope.

The first repair compiled the helper in 28.1 seconds (32.6 seconds in its sandbox
check), but the item sandbox then timed out. Its finite-stage formula similarly
compared maps whose codomains used the concrete tensor tower and the functorial
tower. The same repair is now applied there: `quotientMap R t P n` is explicitly
typed into the functorial tower and defined as
`koszulRepresentativeQuotient R P t n`. `quotientProduct` is the product of these
same maps, and `RepresentativeComparison.quotient_formula` uses their names on
both sides. Unfolding them recovers exactly the original quotient formula. Both
new canonical-map definitions belong to the existing model notion, have its
source/blueprint docstrings, and are listed in that node's `lean.declarations`.

The quotient-map naming brought the helper to 14.8 seconds. The item remained
borderline: one sandbox check timed out and direct server confirmation took 59.5
seconds. Its specialized `RepresentativeComparison` is therefore now a subtype
of the existing generic `RepresentativeRoosComparison`, whose predicate is the
conjunction of exactly the former `quotient_formula` and `computes` fields.
This retains the same data and conditions without generating specialized
recursors/no-confusion/injectivity declarations. The main theorem signature and
every mathematical clause remain unchanged. The first predicate conjunct is the
balanced quotient equation; the second is the normalized exchange equation.

Final repair validation: the two-module `scompile.py` invocation passed cleanly.
The helper's overlay, preliminary, sandbox and library checks each took 14.8
seconds; the item's sandbox took 22.3 seconds and its library check 20.0 seconds.
There were no warnings or errors. Both files retain the default heartbeat setting
and the prescribed 60-second per-file limit. The helper has no `sorry`; the item's
one theorem has the intended `sorry` proof. Line-width and signature-record checks
passed, and a fresh project/Mathlib grep found no pre-existing declaration of the
new names or the exchange statement. No mathematical statement correction or
additional DAG node was needed for this repair.
