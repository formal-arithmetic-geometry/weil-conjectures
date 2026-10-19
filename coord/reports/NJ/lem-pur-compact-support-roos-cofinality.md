## Worker report

This repairs the returned head 9897d8614c8b. The saved packet was inspected and
its prescribed initial dry run passed mechanically at 3bcc0d9876. Reading it
against the return nevertheless confirmed F1--F4, so the packet was repaired
before delivery. The current shared node and saved node initially agreed in
every field other than `lean`; the delivery wrapper refreshes its base.

`Sheaf.CategoryTheory.CompactSupportRoosCofinality` now states the node in two
named theorems: `CategoryTheory.compactSupportRoosCofinality` gives the
cofinal comparisons and `CategoryTheory.compactSupportRoosFiniteFree` gives
the finite-free coefficient clause. Both have proof `sorry`, and their
docstrings carry the corresponding steps 1--5 and 6--7 of the node's proof.
The auxiliary abbreviations only specialize existing constant-sheaf,
module-category, termwise-functor and product-comparison definitions. There
are no postponed definitions, new nodes, or dependency-interface repairs.

Hypotheses, individually:

- The small site is `{C : Type uC} [Category.{vC} C]` with
  `J : GrothendieckTopology C`. Coefficients and modules live in
  `max uC vC r`, containing both site universes without equating them.
- The commutative coefficient ring is `A : CommRingCat.{max uC vC r}`.
  `compactRoosRing J A` is exactly the ring sheaf underlying
  `(constantSheaf J CommRingCat).obj A`.
- `compactRoosModules J A` abbreviates the recorded
  `ringedSiteModules (compactRoosRing J A)`. Thus the theorem is explicitly
  about modules over the constant ring sheaf, rather than an unspecified
  abstract abelian category.
- `HasSheafify` for commutative rings and abelian groups,
  `HasSheafCompose` for forgetting commutative rings to rings, and
  `WEqualsLocallyBijective` supply the standard sheafification and abelian
  category structures on a site of this size. They add no geometric or
  exactness assumption. Countable products are the existing sheaf products.
- `HasExactLimitsOfShape (Discrete ℕ) (compactRoosModules J A)` is the
  assumption that countable products are exact. No such extra assumption on
  B-modules is introduced in the finite-free theorem.
- A strict tower of complexes is `X : CochainComplex
  (ℕᵒᵖ ⥤ compactRoosModules J A) ℤ`. The source's positive index `i`
  is encoded by `op (i-1)`; transitions are the actual functor maps.
- `e : ℕ` and `he : 1 ≤ e` give precisely the positive arithmetic
  restrictions. `complexRestriction` keeps levels `e(n+1)-1` in this encoding.
- The scalar theorem adds `B : CommRingCat`, `Algebra A B`, `Module.Free A B`
  and `Module.Finite A B`, exactly a finite free commutative A-algebra in
  degree zero. Termwise `mapHomologicalComplex` is tensor with that
  degree-zero algebra, with no totalization or derived-category replacement.

Conclusions, individually, and repairs of the numbered return:

1. **F1:** `strictRoosComplex X` is the recorded shifted cone of `1-s`.
   The existential is now one family `ρ X e he`, each a `QuasiIso`.
   In degree `p+1`, `strictRoosCoordinates` orders the target product at `p`
   first and the source product at `p+1` second. The actual equation is
   `biprod.map ((block e X.asFunctor).f p)
   ((selection e X.asFunctor).f (p+1))`. Thus `b_e` acts on the target and
   `a_e` on the source, as in Stacks 0H9K. The formerly reversed equation is
   removed everywhere, including the old report's incorrect description.
2. **F3, naturality:** for every strict tower map `f : X ⟶ Y`, the theorem
   supplies its full and restricted Roos maps `μ` and `μe`. Their two
   coordinate equations require the actual `strictRoosProductMap f` and
   `strictRoosProductMap ((complexRestriction _ e).map f)` on both summands.
   The equation `μ ≫ ρ Y e he = ρ X e he ≫ μe` states naturality for every
   strict tower map, with no arbitrary unnormalized maps.
3. **F3, composition and identity:** the next conjuncts are
   `HEq (ρ X 1 _) (𝟙 (strictRoosComplex X))` and
   `HEq (ρ X e he ≫ ρ ((complexRestriction _ e).obj X) f hf)
   (ρ X (e*f) _)`. Here `HEq` means equality after equality transport between
   the equal reindexed tower complexes. It asserts strict equality before
   localization, and does not substitute a derived or homotopy equality.
4. For every complex `P` and family `γ`, the compatibility equation is
   `γ (n+1) ≫ X.asFunctor.map (homOfLE (Nat.le_succ n)).op = γ n`.
   The theorem supplies `b` and `b'`, normalized by `biprod.lift 0 (Pi.lift γ)`
   and its restricted version, and states `b ≫ ρ X e he = b'`. This is exactly
   the zero target-coordinate augmentation and its selected source family.
5. **F2, construction and B-linearity:** the second theorem supplies an
   additive functor `F` between the two recorded constant-ring-sheaf module
   categories. Its object equality is to
   `SheafOfModules.changeOfRingsOfUniverses` along the constant sheaf map
   induced by `algebraMap A B`; its map `HEq` fixes every morphism to
   `changeOfRingsHomOfUniverses`. These conditions completely determine the
   scalar extension, using the recorded `def-pur-sheaf-tensor-product`
   interface. F is a conclusion, not a new hypothesis or arbitrary choice.
   All target morphisms are B-module sheaf morphisms, hence B-linear.
6. **F2, canonical isomorphism:** `θ X` is an isomorphism of actual complexes
   from termwise F of `strictRoosComplex X` to the Roos complex of the
   termwise-extended tower. Its degreewise equation is F of the existing
   cone coordinate isomorphism, followed by Mathlib's `F.biprodComparison`
   and the two canonical product comparisons. The latter are transparent
   specializations of Mathlib `piComparison`. This fixes the canonical map;
   no finite basis is chosen in its definition.
7. **F2, naturality and cofinal restriction:** the scalar theorem supplies
   normalized full Roos maps for every tower map and states
   `F_complex.map μ ≫ (θ Y).hom = (θ X).hom ≫ ν`. It also supplies the
   normalized `ρ` and `ρB` for every positive e and states
   `F_complex.map ρ ≫ (θ (restriction X)).hom = (θ X).hom ≫ ρB`.
   Each map is fixed by its actual two cone-coordinate equations. Thus
   existence and the canonical normalization are included in both squares.
8. **F2, augmentation:** for every compatible `γ` and normalized augmentation
   `b`, the scalar theorem supplies `bB`, normalizes its source coordinate
   to `Pi.lift (fun n ↦ F_complex.map (γ n))` and its target coordinate to
   zero, and asserts `F_complex.map b ≫ (θ X).hom = bB`.
9. **F4:** `stmt_deps` now additionally names
   `lem-sf-strict-roos-derived-limit-comparison` and
   `lem-sp-strict-tower-arithmetic-restriction`. Their recorded modules are
   publicly imported and their actual constructions are used. Traversing
   statement and proof dependencies from both nodes found no route back to
   this item (167 and 160 visited nodes, respectively), hence no cycle.

Dependency declarations read and used:

- `Mathlib.CategoryTheory.Sites.ConstantSheaf`:
  `CategoryTheory.constantSheaf`, sheafification of the constant presheaf.
- `Sheaf.CategoryTheory.RingedSiteModules`:
  `CategoryTheory.ringedSiteModules`, exactly Mathlib `SheafOfModules`.
- `Mathlib.CategoryTheory.Functor.OfSequence`:
  `CategoryTheory.Functor.ofOpSequence` and the functor/natural-transformation
  encoding of inverse towers.
- `Mathlib.Algebra.Homology.DerivedCategory.Basic`: the recorded cochain,
  quasi-isomorphism and derived-category conventions; no conclusion is
  weakened by passing to the derived category.
- `Sheaf.CategoryTheory.StrictRoosDerivedLimitComparison`:
  `strictRoosProduct`, `strictRoosComplex`, `strictRoosCoordinates`, and
  `strictRoosProductMap` in namespace `CategoryTheory`.
- `Sheaf.CategoryTheory.StrictTowerArithmeticRestriction`:
  `index`, `complexRestriction`, `selection`, and `block` in namespace
  `CategoryTheory.StrictTowerArithmetic`.
- `Sheaf.Algebra.Category.ModuleCat.Sheaf.SiteTensorFunctoriality`, publicly
  importing `TensorProductOfUniverses`: the recorded
  `SheafOfModules.changeOfRingsOfUniverses` and
  `changeOfRingsHomOfUniverses`, which sheafify sectionwise scalar extension
  with its target-ring action. No separate tensor product is defined.
- `Mathlib.LinearAlgebra.TensorProduct.Basic`: the tensor universal property
  used in proof steps 6--7, imported for the recorded proof dependency.
- Mathlib `mapHomologicalComplex`, `whiskeringRight`, `piComparison`, and
  `Functor.biprodComparison`: existing canonical functors and comparisons.

Edge cases checked against the formulas: e=1, e=2 and the omitted initial
level; zero, identity, nonsurjective and zero-transition towers; zero
complexes; negative degrees; zero augmentations; the empty site; finite-free
rank zero (the zero coefficient algebra) and rank one. For the reported
constant Z-module tower counterexample, the corrected equation reads
`block D = D_e selection`, so it no longer asks the false equation
`selection D = D_e block`. A finite arithmetic check for 1≤e,f≤7 and
0≤n<20 verified all 980 iterated-index identities and block partitions.
Only finite transition sums occur, so no surjectivity or convergence
assumption has been introduced.

Searches: the retained packet searched LeanFinder, LeanSearch, Loogle,
Mathlib, upstream `WeilConjectures/`, and the side project for cofinal Roos
maps; no exact statement was found. Repair searches were repeated with
`msearch.py leanfinder` query "Roos complex finite free scalar extension
commutes with countable product cone cofinal restriction" (eight unrelated
Condensed/Profinite results), `msearch.py loogle '"biprodComparison"'`
(found Mathlib's canonical biproduct comparison, used verbatim), and
`msearch.py grep 'changeOfRings.*Functor|extendScalars'
Algebra/Category/ModuleCat` (ordinary ModuleCat scalar extension, no sheaf
Roos comparison). Direct `rg` over the named upstream and side directories
for the item id, `compactSupportRoos`, and helper names found no duplicate.
The sectionwise change-of-rings interface was found and read in
`TensorProductOfUniverses`, and the recorded current tensor module was
read in full. Mathlib's product-comparison source was read; the helper is
an abbreviation of that declaration, not a replacement.

The source's Stacks passages 0H9K (selection/block square and composition)
and 0941 (Roos model) were reopened locally, and all seven proof steps of
the current node were reread. No change to the mathematical node statement
is needed. No `STATEMENT-DISPUTED` flag remains. All mathematical proofs
remain `sorry` as required for stage 2; every abbreviation has actual data.

## Second reading by NJ

I compared the returned packet, the current node and the revised module.
F1 was present in the saved Lean and report: both now put block on the
first, target coordinate and selection on the shifted source coordinate.
F2 was only prose: it is now a separate recorded theorem with constant
A- and B-ring sheaf module categories, the recorded scalar extension on
objects and maps, a B-linear isomorphism with fixed product/biproduct
coordinates, and explicit naturality, cofinal and augmentation squares.
F3 was absent: the cofinal theorem now supplies a single family for all
X and e, gives the strict tower-map naturality square, and states identity
and composition using equality transport. F4 is repaired by the two added
landed statement dependencies, whose dependency closures were checked.

The site, commutative ring, exact-product hypothesis, strict tower,
positive restriction index, both cone coordinates and every augmentation
quantifier match the node. The coefficient theorem adds exactly a finite
free commutative A-algebra and uses ordinary termwise tensor extension.
The choice of finite basis occurs only in the proof plan for invertibility;
the comparison itself is fixed by canonical projections. There is no
assumed comparison map, no hollow construction, and no omitted scalar
clause. Both theorem proofs are `sorry`. Every universe is named and all
variables are bound under `autoImplicit false`. The report lists each
hypothesis and each conclusion, including the repaired clauses.
