## Worker report

The module `Sheaf.Paper.IntrinsicKoszulCompletion` defines the positive-power Koszul
tower, its constant sheaf complexes and total tensors, the termwise product, one minus
shift, the specified shifted mapping cone, its completion unit, and intrinsic completeness.
The node statement is unchanged. There are no new nodes and no disputed statements.

Hypotheses and clauses, in the order of the node:

- The scheme is `X : Scheme.{t}`. The site is the recorded `X.ProEt` and
  `ProEt.topology X`, with object universe t+1 and morphism universe t. The ring sheaves
  `adicConstantRing X Λ`, `adicModuleRing X Λ`, and the derived category
  `proEtaleDerivedCategory X Λ` are exactly those of the recorded coefficient datum.
- The commutative ring is `Λ : Type t` with `[CommRing Λ]`. Its Noetherian property,
  ideal I, finite generation, additive torsion of Λ/I, and perfectness of all positive
  quotient powers are the fields of `d : CompleteCoefficientDatum Λ`. There is no
  I-adic completeness, regular-sequence, boundedness, or finite-quotient assumption.
- `r : ℕ` includes r=0; `f : Fin r → Λ` lists the generators, and
  `hf : Ideal.span (Set.range f) = d.ideal` identifies their ideal with I.
- `K : proEtaleDerivedCategory X Λ` is arbitrary. The fixed representative is an
  explicitly supplied complex C, its `CochainComplex.IsKFlat` proof over
  `adicConstantRing X Λ`, and `e : (adicLocalization X Λ).obj C ≅ K`.
  In particular no flat-terms assumption is added. K-flat resolution availability is
  already supplied by `CochainComplex.exists_isKFlatResolutionGeneral`; choosing the
  representative is input, as in the node, rather than arbitrary data chosen by sorry.
- `koszulPower Λ r f n` is the recorded `ExteriorAlgebra.koszulComplex` for powers
  n+1, extended along `ComplexShape.embeddingDownNat`. Thus chain degree a becomes
  cochain degree -a, with the same differential. `ULift Λ` is the ring-universe lift
  already used by the constant coefficient sheaf, not a different coefficient ring.
  The recorded exterior powers vanish above r, so the support is [-r,0].
- `koszulPowerGenerator` sends e_j to f_j e_j by `Finsupp.linearCombination`.
  Its exterior power gives every component of `koszulPowerTransition`; extending
  this chain map gives t_m in cohomological indexing. The commutation equation is
  a named postponed theorem with the generator computation in its docstring.
- The degree-zero unit is `exteriorPower.zeroEquiv.symm`, transported through the
  constant-module functor and the extension's degree-zero isomorphism in
  `koszulSheafUnitZero`. `koszulSheafUnit` is u_m as a complex map. The preliminary
  map `koszulConstantOne` is selected from a UNIQUE existence theorem specifying
  the image of 1 on EVERY site object; a mere arbitrary nonempty map is not used.
- `koszulPowerSheaf` applies module sheafification to the actual constant module
  presheaf, with the coefficient action extended along the commutative-ring
  sheafification unit. `koszulConstantUnit_local` states the two local bijectivity
  facts needed by this construction. The associated proof is postponed by name.
- `koszulTensor` is `CochainComplex.mapBifunctor` of C and this constant Koszul
  complex, using the SAME `SheafOfModules.monoidalCategory (adicConstantRing X Λ)`
  as the recorded derived tensor. This is the total differential
  d_C tensor 1 + (-1)^p 1 tensor d_Q. K-flatness makes it the derived tensor.
- `koszulTensorTransition` is the bifunctor map of identity on C and t_m.
  `koszulProduct` is `∏ᶜ` of these complexes, whose terms are termwise products by
  Mathlib's homological-complex limits. `koszulOneSubShift` is the identity minus
  `Pi.lift (fun n ↦ Pi.π M (n+1) ≫ transition n)`, giving precisely the specified
  projections of s. Index n=0 means m=1 throughout; no m=0 stage is inserted.
- `koszulCompletionComplex` is the actual Mathlib `mappingCone` of 1-s, shifted
  by -1. Mathlib orders its degree-a summands as P^a followed by P^(a-1).
  Reading them in the node's order (y,x) gives exactly
  (-d_P y -(1-s)x, d_P x), including both minus signs.
  The imported exact-products and derived-products dependencies justify the Rlim
  notation for this fixed model; the construction does not choose a triangulated cone.
- `koszulTensorUnitComponent` uses the inverse RIGHT unitor, tensors with the
  degree-zero unit, and includes the (p,0) summand of the total tensor.
  Thus it is exactly c ↦ c tensor 1. Its chain-map law is separately named.
  `koszulProductUnit` assembles these maps with `Pi.lift` to give a:C→P.
- `koszulCompletionUnitComplex` has the actual component a^p followed by
  `homotopyCofiber.inlX`, into the source summand P^p of the shifted cone.
  This is (0,a(c)) in the node's ordering. Its named commutation theorem uses
  t_m(1)=1 and therefore a(1-s)=0. There is no unspecified map of Roos triangles.
- `intrinsicKoszulCompletion` localizes that shifted cone with the recorded
  `adicLocalization`. `intrinsicKoszulCompletionUnit` is
  `e.inv ≫ (adicLocalization X Λ).map koszulCompletionUnitComplex`, hence starts
  at the given K. `IsIntrinsicallyDerivedComplete` is exactly `IsIso` of this map.

All definition data are real constructions. The only choice from a postponed theorem
is the uniquely specified constant unit map; the theorem fixes the map by all its
section values on 1. The other postponed declarations are well-definedness/chain-map
laws of the construction, each named with the owning DAG id and a natural-language proof.
Every theorem body is `sorry`; no mathematical proof has been supplied at stage 2.

Dependency declarations read and used:

- `Sheaf.AlgebraicGeometry.ProEtaleDerivedCategory`:
  `AlgebraicGeometry.Scheme.proEtaleDerivedCategory`.
- `Sheaf.Paper.CompleteCoefficientDatum`: `CompleteCoefficientDatum`,
  `adicConstantRing`, `adicModuleRing`, `adicLocalization` (namespace
  `AlgebraicGeometry.Scheme`). Its `AdicKFlatModel` was read but is not used,
  because it adds flat terms to a chosen model whereas this node only fixes K-flatness.
- `Sheaf.Paper.KoszulComplex`: `ExteriorAlgebra.koszulComplex` and its contraction
  differential on the exterior powers.
- `Sheaf.Algebra.Homology.DerivedTensor`:
  `AlgebraicGeometry.Scheme.derivedTensor`, read to retain its exact tensor construction.
- `Sheaf.Algebra.Homology.KFlatResolutionGeneral`:
  `CochainComplex.exists_isKFlatResolutionGeneral` (proof dependency import).
- `Sheaf.AlgebraicGeometry.ProEtaleCountableProductsExact`:
  `AlgebraicGeometry.Scheme.ProEt.countableProducts_exact` (proof dependency import).
- `Sheaf.CategoryTheory.Triangulated.DerivedLimitProducts`:
  `CategoryTheory.derivedCategory_countableProducts_core` (proof dependency import).
- `Mathlib.Algebra.Homology.DerivedCategory.Basic`: `DerivedCategory`,
  `HasDerivedCategory`, `DerivedCategory.Q`, with the standard localization already
  fixed by the recorded pro-etale derived category.
- `WeilConjectures.CategoryTheory.Triangulated.DerivedLimit`:
  `CategoryTheory.IsDerivedLimit`, `IsDerivedLimitTriangle`. The current source was
  read with `scompile.py --source`, since it is absent in the older local source tree.
- The added landed dependency `def-sf-site-constant-module-functor` supplies
  `CategoryTheory.siteConstantModulePresheafGeneral` after the universe-only repair
  described below. No duplicate general notion is introduced under a new DAG node.

Edge cases checked: r=0 gives the coefficient complex in degree zero and identity
transitions; the empty set of generators gives the zero ideal. Zero generators and
zero divisors are permitted (no regularity is used). The zero ring, unit ideal, zero
complex, and empty scheme are allowed by the definitions. Products remain infinite
for r=0 and for a zero complex. Unbounded C is allowed; coproducts in the tensor total
are the existing ones. Checking m=1 confirms f^1 as the first differential and f as
the transition multiplier from f^2; this excludes an indexing shift. Checking r=1
confirms t_m d_m = d_(m+1) and the completion-unit cone signs.

Searches for existing declarations:

- `msearch.py ... leanfinder "intrinsic Koszul derived completion inverse limit tensor
  Koszul complexes"`: eight results about ordinary adic completion and Kähler
  differentials; none defines the intrinsic derived Koszul completion.
- `msearch.py ... loogle "CochainComplex.mappingCone"`: twelve mapping-cone results;
  the mapping cone exists and is reused, but no Koszul completion definition.
- `msearch.py ... grep "koszul|Koszul"`: only regular-sequence TODO, local cohomology
  documentation, and covariant-derivative terminology in Mathlib.
- `msearch.py ... grep "homotopyLimit|derivedCompletion|koszulCompletion"`: no hits.
- `msearch.py ... leansearch "intrinsic Koszul derived completion inverse limit of
  Koszul powers"`: service unavailable (Internal Server Error), recorded as unavailable.
- `rg` of `WeilConjectures` for `koszul|Koszul|intrinsic` found Koszul sign/braiding
  constructions, projective-line Koszul sequences, and intrinsic constructibility;
  none defines this completion. Search for the full item id returned no hits.
- `rg` of `lean/Sheaf` found the recorded Koszul complex, shifted augmentations,
  and constant-module functors. Their definitions were opened; none defines this tower
  completion. Searches for the proposed main declaration and well-definedness names
  in both source libraries returned no hits.

Validation: both delivered files compiled separately through the prescribed scompile.py
wrapper, in dependency order, with `autoImplicit false`, no errors and no warnings.
The generalized constant module file took about 1.8 seconds; the main file about
8.6 seconds. No Lake/global build or live-source edit was performed.

## Dependency modules

`def-sf-site-constant-module-functor`: its recorded
`CategoryTheory.siteConstantModuleFunctor` binds C : Type u with SmallCategory C,
and modules/rings in universe u. In particular it cannot accept the small pro-etale
site as actually recorded (object universe t+1, morphism universe t). The repair
`Sheaf.CategoryTheory.SiteConstantModuleFunctorGeneral` retains the same constant
module presheaf with identity restrictions and componentwise linear maps, followed by
module sheafification along the constant ring sheafification unit, but separates
site object and morphism universes. Coefficients and modules live in max u v.
The main module uses its generalized constant-presheaf declaration, sheafifying
along the unit obtained by forgetting commutativity from the constant COMMUTATIVE
ring sheaf, so its coefficients are definitionally the recorded `adicModuleRing`.
Only this dependency node's lean record changes, with the required explanation;
its statement, mathlib_match and other fields are preserved.


## Second reading by ND

Independent second reader: I opened the sandbox node and both delivered modules,
the source blueprint definition at order 1257 and its coefficient/adic-limit context,
and the declarations of the recorded dependencies. The node is a definition with
empty proof/proof_deps; no theorem or target statement is being corrected.

The node's objects, hypotheses, and clauses, matched in order:

1. Scheme X and its small pro-etale site: `X : Scheme.{t}`, `X.ProEt`,
   `ProEt.topology X`, and `proEtaleDerivedCategory X Λ`. Verdict: exact. I read
   `ProEtaleDerivedCategory.lean`; its coefficient ring is the constant commutative
   ring sheaf with commutativity forgotten, and its localization is the standard one.
2. Commutative Noetherian coefficient ring, finitely generated ideal, torsion quotient,
   and perfect positive quotient powers: `[CommRing Λ]`, `d : CompleteCoefficientDatum Λ`.
   I opened its structure: `ideal`, `noetherian`, `finitelyGenerated`, `quotientTorsion`,
   and `quotientPerfect` carry precisely these conditions. Verdict: exact; no adic
   completeness or finite underlying quotient is assumed.
3. Finite generator list and its ideal: `r : ℕ`, `f : Fin r → Λ`, and
   `hf : Ideal.span (Set.range f) = d.ideal`. Verdict: exact, including r=0.
4. Arbitrary derived object and fixed K-flat representative: `K`, `C`,
   `hC : CochainComplex.IsKFlat (R := adicConstantRing X Λ) C`, and
   `e : (adicLocalization X Λ).obj C ≅ K`. Verdict: exact. The imported general
   resolution theorem supplies K-flat resolutions without identifying the two site
   universes. The stronger flat-terms field of `AdicKFlatModel` is correctly avoided.
5. Positive-power Koszul complex and cohomological reindexing: `koszulPower` uses
   the recorded `ExteriorAlgebra.koszulComplex` at `f j ^ (m+1)` and extends along
   `ComplexShape.embeddingDownNat`. I opened both definitions: the differential is
   contraction and the embedding sends a to -a without a sign change. Verdict: exact.
6. Transition exterior map e_j ↦ f_j e_j: `koszulPowerGenerator`,
   `exteriorPower.map`, and `koszulPowerTransition`. Verdict: exact. The source is
   the (m+2)-power stage and target the (m+1)-power stage. The named commutation
   theorem has the correctly oriented equation and the generator proof in its docstring.
7. Degree-zero identity unit: `koszulConstantOne`, `koszulSheafUnitZero`, and
   `koszulSheafUnit`. Verdict: exact. `exteriorPower.zeroEquiv.symm` identifies the
   coefficient module with wedge degree zero. `koszulConstantOne_exists` specifies
   every section value on 1 and states uniqueness; its choice is not arbitrary data.
8. Constant Koszul sheaf complex: `koszulConstantUnit`, `koszulConstantFunctor`,
   and `koszulPowerSheaf`. Verdict: exact. I read Mathlib's module sheafification:
   its underlying sheaf is the sheafification of the input abelian presheaf, with
   the scalar action extended along the given locally bijective ring map.
9. Total tensor M_m and its transitions: `koszulTensor` and
   `koszulTensorTransition`. Verdict: exact. I opened `derivedTensor` and checked
   the same `SheafOfModules.monoidalCategory (adicConstantRing X Λ)` and total
   bifunctor construction; the tensor factors are C followed by Q, with differential
   d_C tensor 1 + (-1)^p 1 tensor d_Q.
10. Termwise product P and shift s: `koszulProduct` is the product in cochain
    complexes; `koszulOneSubShift` is identity minus the `Pi.lift` whose nth
    component is the (n+1)st projection followed by the tower transition. Verdict:
    exact. I read the countable-products and derived-products dependency statements;
    the cone uses the actual product complex, without choosing a triangulated limit.
11. Completion with specified cone differential: `koszulCompletionComplex` is
    `(CochainComplex.mappingCone (koszulOneSubShift ...))⟦(-1 : ℤ)⟧`.
    Verdict: exact. I checked Mathlib's `homotopyCofiber.d` and `shiftFunctor`:
    cone coordinates are (source^{a+1}, target^a) with differential
    (-d_source x, φ x + d_target y). Shifting by -1 and reading coordinates
    as (y,x) gives (-d_P y - φ x, d_P x), exactly the node's signs.
    `intrinsicKoszulCompletion` applies the recorded localization to this complex.
12. Compatible unit family a: `koszulTensorUnitComponent` uses the inverse right
    unitor, tensors with the degree-zero unit, and includes the (p,0) total summand;
    `koszulTensorUnit` and `koszulProductUnit` assemble it. Verdict: exactly c ↦ c tensor 1.
13. Completion unit κ_K: `koszulCompletionUnitComplex` includes a into the source
    summand of the shifted cone via `homotopyCofiber.inlX`; in the node's ordering
    this is (0,a(c)). `intrinsicKoszulCompletionUnit` precomposes its localized map
    with `e.inv`, so its domain is K. Verdict: exact, with no unspecified Roos lift.
14. Intrinsic derived I-completeness: `IsIntrinsicallyDerivedComplete` is `IsIso`
    of that very unit, with the same fixed representative arguments. Verdict: exact.

Edge cases: r=0 is accepted, so I=0 and Q is the degree-zero coefficient complex;
the tower still starts at positive exponent one and has identity transitions in this
case. Zero and repeated generators and zero divisors are unrestricted. The zero ring,
zero complex, unit ideal and empty scheme introduce no excluded case. C can be
unbounded in both directions. There is no characteristic restriction. The universe t
is arbitrary; site objects remain in t+1 and arrows in t, with the canonical ULift of
coefficients to t+1. No additional equality of universes or finiteness instance appears.

Dependency-module reading: I also opened the original constant-module dependency node,
its original `SiteConstantModuleFunctor.lean`, the delivered generalized module, and
Stacks `sites-modules.tex`, Tags 03CY and 093T. The original `[SmallCategory C]` ties
object and arrow universes together and is unusable for the recorded site. The repair
separates them and uses coefficient/module universe max u v. Its constant presheaf has
value M, identity restrictions, and componentwise f on morphisms; its functor then
sheafifies along the constant ring sheafification unit. This is exactly the dependency
node's construction. Tag 03CY needs only a site and presheaves of rings/modules;
finite presentation assumptions in Tag 093T concern Hom/Isom comparisons and are not
hypotheses of the constant-module construction. Verdict: authorized §1(B) repair;
only the dependency's lean record is changed, with an explanatory note. No new nodes.

Independent searches: LeanFinder query "homotopy inverse limit completion by powers
of finitely generated ideal Koszul" returned eight ordinary adic-completion results,
none a Koszul completion. Loogle `CochainComplex.mappingCone` returned the existing
cone API, which this delivery uses. LeanSearch "derived completion of a complex using
Koszul powers" was unavailable (Internal Server Error). I ran rg on Mathlib,
WeilConjectures, and lean/Sheaf for derivedCompletion, koszulCompletion,
intrinsicallyDerivedComplete, and Koszul/limit combinations, and searched the upstream
name index. I opened the tempting upstream `DerivedCategory.derivedCompletionDiagram`,
`derivedCompletionCone`, and `derivedComplete` in Complete/Defs.lean: these concern
K tensor R/I^n and a homotopy-limit property of the cone with point K, not the specified
Koszul complex model and unit here. The project Koszul-Hom colimits and extended Čech
complexes are likewise different. Searches for constant module functors found the
recorded small-site construction and specialized étale/topological constructions;
none supplies the needed independent site universes in this encoding. No duplicate
notion was found.

Mismatches and changes: none found in the Lean or node records; both modules and
both node records are retained unchanged. This second-reading section is the only
review edit. All definition data are constructions, and the one postponed existence
used for data is uniquely characterizing. Named well-definedness statements have
source/blueprint docstrings and natural-language proofs; theorem bodies remain sorry.
No unbound variable or universe was found, and all lines satisfy the 100-character rule.
The normalized recorded lean.statement signatures agree verbatim with the files.

Validation repeated independently: scompile.py compiled both sibling files separately,
in dependency order, with no errors or warnings (about 1.7 s and 8.0 s for the library
checks). An initial invocation from the repository directory failed to locate the
sandbox-only file; rerunning from the sandbox resolved that path error. No direct Lean
build, global build, live-source edit, or git command was performed.
