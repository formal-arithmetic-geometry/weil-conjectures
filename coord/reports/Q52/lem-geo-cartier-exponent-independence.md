## Worker report

The module `Sheaf.Paper.GeoCartierExponentIndependence` states
`SheafOfModules.GeoCartierExponent.geoCartier_exponent_independence`.
Every theorem proof is `sorry`. Definitions contain actual maps, functors,
isomorphisms, and the recorded universal counit. No mathematical statement,
statement dependency, proof, or proof dependency of the node is changed.

The source is the current blueprint main-20261015 Cartier proof, paragraph 4,
together with the node's explicit auxiliary exponent comparison. That paragraph
constructs the single-exponent class; it does not itself assert independence.
I also read Stacks sites-cohomology.tex, `lemma-derived-base-change` (06YY),
`lemma-derived-pullback-composition` (0D6D), and `lemma-adjoint` (07A6), and
derived.tex, `lemma-derived-canonical-delta-functor` (0152). The theorem docstring
includes all eight steps of the DAG proof, including the local kernel calculation
and the two-adjunction argument that determines the actual map and its sign.

Hypotheses and objects, matched to Lean:

- A small site with final object is represented by `C : Type u`,
  `[Category.{v} C]`, `[EssentiallySmall.{r} C]`, a Grothendieck topology `J`,
  and `[HasTerminal C]`. Sheafification, sheaf composition, and locally bijective
  equivalences are the standard infrastructure for these module categories.
  As in the recorded general-site dependencies, the associated topology describes
  sheaves, rather than choosing a new precoverage presentation of the site.
- The positive exponents and divisibility are exactly `hm : 1 ≤ m`,
  `hn : 1 ≤ n`, and `h : n ∣ m`.
- The constant integer and residue rings are the recorded
  `DivisibleReduction.integers J` and `DivisibleReduction.residues J q`.
  They are constant sheafifications of `ULift ℤ` and `ULift (ZMod q)`.
  The initial ring map is `DivisibleReduction.projection J q`.
  `residueProjection h` is the actual constant sheafification of
  `ZMod.castHom h (ZMod n)`, transported through ULift.
- `Dm`, `Dn`, and `Dmn` are the recorded
  `DerivedChangeOfRingsCochainModel`s for precisely those three ring maps.
  Their ordinary objects/maps are the actual sheafified scalar extensions;
  their derived functors and counits have the universal derived property.
  Source and target derived morphism universes `wZ`, `wM`, `wN` are independent.
  No flatness of the coefficient ring map is imposed.
- `Pm` and `Pn` are the dependency's existing `DivisibleReduction.Presentation`s.
  The common abelian sheaf B is their `S.X₁`, and F is their `S.X₃`;
  `hB` and `hF` identify those same endpoints between the two presentations.
  The middle extension is auxiliary and is never used in the conclusion.
  These are presentations of the hypotheses, not an added existence restriction:
  for every B,F in the node one can take `0 -> B -> B ⊞ F -> F -> 0`
  at both moduli, exactly as step 2 of the DAG proof instructs.
  The existing `presentation_exists` supplies its presentations.
- `Pm.H` and `Pn.H` are the torsion sheaves, with their natural residue actions.
  Their maps `i`, equations `wi`, and `kummer.ShortExact` specify exactly
  `0 -> H_q -> B ->[q] B -> 0`. Thus q is epi on B and H_q is its kernel.
- `Pm.Q` and `Pn.Q` are the quotient sheaves. Their maps `p`, equations `wp`,
  and `quotient.ShortExact` specify exactly `0 -> F ->[q] F -> Q_q -> 0`.
  Thus q is mono on F and Q_q is its sheaf cokernel. All categorical epis here
  mean local surjectivity, not surjectivity on global sections.
- Flatness is exactly `hH : IsFlatOnSite (R := residues J m) Pm.H` and
  `hQ : IsFlatOnSite (R := residues J m) Pm.Q`. This uses the dependency's
  exact sheaf tensor functor. Flatness at n is not assumed.

Conclusions, matched clause by clause:

- The two ordinary scalar-extension isomorphisms are existential isomorphisms
  `eF : changeOfRings (residueProjection h) Pm.Q ≅ Pn.Q` and
  `eH : changeOfRings (residueProjection h) Pm.H ≅ Pn.H`.
  Ordinary tensors use the dependency's scalar-first convention `b tensor x`.
- The first section formula says that `eF` sends the sheafification image of
  `b tensor Pm.p(f)` to `b • Pn.p(f)`, transporting f only by `hF`.
  `SuccessiveDerivedQuotient.pure` is the existing sheafified pure tensor.
  Since the quotient projections are epis, local representatives cover every
  quotient section; no global representative is assumed.
- `beta : Pm.H -> (residueRestriction h).obj Pn.H` is R_m-linear.
  The second clause says after the actual inclusion into B that
  `Pn.i (beta x) = (m / n) • Pm.i x`, with the common B identified by `hB`.
  Monicity of `Pn.i` fixes beta uniquely; this is not an unconstrained map.
- The third clause gives the full torsion formula for every local residue scalar:
  `eH(b tensor x) = b • beta(x)`. Together with the preceding inclusion equation
  this is exactly `b(m/n)x`, including `x tensor 1 -> (m/n)x`, or `x^(m/n)`
  in multiplicative notation. Using beta avoids pretending an arbitrary local
  residue scalar acts on B before choosing a local integer lift.
- The last two equalities assert that these are the maps induced by the actual
  `a_F` and `a_B`. Each left side is the conjugate of `transitivity.hom.app`
  by the recorded `DivisibleReduction.identifications` and derived extension
  of the endpoint equality. The quotient right side is `ordinarySingle`
  followed by the degree-zero map of `eF`. The torsion right side is the canonical
  shift comparison followed by the shift of `ordinarySingle` and of `eH`.
  Thus the result includes comparison of maps, not just the existence of two
  ordinary isomorphisms.
- The recorded `identifications m Dm hm Pm` and its n version include the
  `quotient_unit` and `kummer_unit` equations. Their `alphaB` is normalized
  using the actual short-exact-sequence boundary `DivisibleReduction.kappa`.
  The statement therefore fixes precisely the requested connecting-morphism sign.

Canonical helper definitions:

`projection_comp` is the coefficient triangle implicit in the item's composable
ring maps; its proof docstring gives integer-cast extensionality and functoriality.
`restrictionComp` uses the existing `ModuleCat.restrictScalarsComp'App` on
sections, the existing presheaf isomorphism constructor, and the fully faithful
forgetful functor. Its maps are identity on underlying sections.
`derivedRestrictionComp` is its canonical derived localization.
`transitivity` is `Adjunction.leftAdjointUniq` for the composite of the recorded
normalized scalar adjunctions and the direct normalized adjunction, transported
by that exact restriction comparison. The unit uniqueness identity characterizes
the same canonical transitivity as the recorded successive-normalization node.
This concrete specialization handles separate localization universes without
introducing any arbitrary comparison or choosing a bare Nonempty isomorphism.
`ordinarySingle` is the existing cochain universal counit followed by the existing
single-complex comparison and the model's prescribed object equality. Its data
is defined for every module; flatness makes that canonical map invertible in
the theorem. No tensor or derived-category construction is duplicated.

Dependency declarations read and used:

- `Sheaf.CategoryTheory.SiteCoveringAxioms`:
  `CategoryTheory.Precoverage.IsSiteForCoverings` (site convention).
- `Sheaf.CategoryTheory.RingedSiteModules`:
  `CategoryTheory.ringedSiteModules`, transparently Mathlib's `SheafOfModules`.
- `Mathlib.Algebra.Homology.DerivedCategory.Basic`:
  `DerivedCategory`, `HasDerivedCategory`, `Q`, and `singleFunctor`.
- `Sheaf.Algebra.Homology.DerivedChangeOfRingsCochainModel`:
  `SheafOfModules.DerivedChangeOfRingsCochainModel`, its prescribed ordinary
  objects/maps, universal counit, and derived functor.
- `Sheaf.Algebra.Homology.SheafRingDerivedCoefficientAdjunction`:
  `SheafOfModules.sheafRingDerivedCoefficientAdjunction` (proof import);
  its normalized cochain implementation is the existing
  `sheafScalarDerivedAdjunction` in the reduction dependency.
- `Sheaf.Algebra.Homology.SuccessiveDerivedQuotientNormalization`:
  `SheafOfModules.SuccessiveDerivedQuotient.pure`, `Normalization.unit_comp`,
  and `successive_derived_quotient_normalization` (canonical characterization).
- `Mathlib.CategoryTheory.Sites.ConstantSheaf`:
  `CategoryTheory.constantSheaf`, used by the recorded rings and by the modulus map.
- `Sheaf.Algebra.Category.ModuleCat.Sheaf.FlatOnSite`:
  `SheafOfModules.IsFlatOnSite`.
- `Sheaf.Paper.DivisibleExtensionDerivedReduction`:
  `DivisibleReduction.Presentation`, `presentation_exists`, `integers`,
  `residues`, `projection`, `Integral`, `Residue`, `restriction`,
  `derivedRestriction`, `Identifications`, `identifications`, and
  `divisible_extension_derived_reduction`; also the normalized scalar adjunction
  and its canonical shift instance.

All recorded proof-dependency modules are imported, including the bounded-above
flat K-flat theorem, K-flat resolution, tensor construction, long exact homology,
short-exact-sequence triangle, and single-object full faithfulness.

Edge cases checked before writing:

- m=n: the coefficient projection is the identity modulo the canonical constant
  ring identification, d=1, and the stated formulas give quotient and torsion
  identities. Different universal derived presentations are handled canonically.
- n=1: R_n is the zero ring; Q_n=H_n=0. Both isomorphism targets and both formulas
  vanish. m=1 forces n=1. No nontrivial-ring hypothesis excludes these cases.
- Zero sheaves, including B=0 or F=0, satisfy the same statements.
- A site with degenerate or empty covers causes no sectionwise-surjectivity
  assumption. Kernel and cokernel statements and the proof are sheaf-local.
- General sites without points are included. Local lifting in the proof uses
  epimorphisms, not geometric stalks or enough points.
- The n=0 case is excluded exactly by the node's positivity hypotheses.
- The underlying coefficient universe and all three localization universes remain
  explicit. No extra equality of site-object and site-morphism universes is imposed.

Searches for an existing statement:

- `msearch.py` LeanFinder, query "derived scalar extension modulo m then n
  identifies quotient and torsion with multiplication by m divided by n": eight
  hits, led by `Submodule.instIsScalarTowerQuotientSpanSingletonSetSubtypeMemTorsionBy`
  and `Submodule.torsionBy.mk_ideal_smul`; these concern ordinary torsion modules,
  not the normalized derived comparison for sheaves.
- `msearch.py` Loogle, query `ModuleCat.extendScalarsComp`: eleven hits, including
  `ModuleCat.extendScalarsComp`, `extendScalarsComp_hom_app_one_tmul`, and
  `homEquiv_extendScalarsComp`. They concern ordinary module scalar extension.
- `msearch.py` grep in `Algebra/Category/ModuleCat`, query
  `derived.*[Rr]educt|[Rr]educt.*derived|[Dd]ivisible.*[Tt]ensor|[Tt]ensor.*[Dd]ivisible`:
  zero hits.
- `rg` in upstream `WeilConjectures` and in `lean/Sheaf`, queries
  `cartier.*exponent|exponent.*independence|DivisibleReduction|SuccessiveDerivedQuotient`:
  found the two recorded dependencies, Cartier coefficient-extension consumers,
  and `SecSmoothPurity/ScalarExtensionFunctor.lean`. The latter's signed Kummer
  comparison concerns Tate twists on schemes and is not this arbitrary-site
  divisible-sheaf/quotient theorem. I read the relevant source sections.
- Upstream search for the exact node id returned no declaration; search in
  `dag/lean_names_upstream.json` likewise found no exact binding. Searches for
  the new fully qualified namespace and declaration names found no collision.

No statement fault, disputed statement, new node, or dependency-node repair.

Validation: the first prescribed file compile identified an elaboration timeout
in an implicit restriction comparison and two missing residue-action type hints.
The explicit identity-on-sections comparison and `@id` type hints fixed these.
The next compile passed both the sandbox and final module name, with only a
101-character line warning. That line was wrapped before the delivery dry run.

The prescribed `deliver2.py --no-push` completed successfully: commit
`5e31aada4e` passed server preflight and per-file compilation with no remaining
warnings. The final module has explicit auto-implicit prohibition and a maximum
line width of 88 characters. Only the item's `lean` field differs from its base.

## Second reading by Q52

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
