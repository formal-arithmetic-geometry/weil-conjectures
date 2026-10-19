## Worker report

The module states the prime-coefficient constructibility theorem, with `sorry` as its only
proof. Its docstring preserves all seven proof steps and their node citations. Source read:
Stacks more-etale.tex, label lemma-proper-smooth-family-curves (0GKV), specifically the
Noetherian paragraph and its cases (a) and (b). No node statement correction is needed:
the node is the Noetherian finite-field-module form of that lemma.

Clause matching:
- Schemes C and S: `{C S : Scheme.{u}}`.
- Noetherian base: `[IsLocallyNoetherian S] [CompactSpace S]`, exactly the two constituent
  properties of Mathlib `IsNoetherian S`.
- Proper morphism: `(f : C ⟶ S) [IsProper f]`. Universally closed already implies
  quasi-compact, so the recorded locally-finite-type presentation is finite type here.
- Smooth morphism: `[Smooth f]`.
- Nonempty geometrically connected fibres: `[GeometricallyConnected f]`. This class
  quantifies over field-valued base points; `ConnectedSpace` includes nonemptiness and
  it induces geometrically connected residue-field fibres. No irreducibility is imposed.
- Dimension exactly one: `h_dim : ∀ s : S, topologicalKrullDim (f.fiber s) = 1`.
  Dimension of a finite-type scheme over a field is invariant under field extension;
  the proper smooth fibres are finite type, so this is also geometric fibre dimension one.
- Every prime ell: `(ell : ℕ) [Fact ell.Prime]`. `ZMod ell` is the prime field, lifted
  to `ULift.{u + 1} (ZMod ell)` to fit the existing coefficient-category universe.
- Every q ≥ 0: `(q : ℕ)`, coerced to ℤ for the homology functor.
- Constant prime-field sheaf: `(constantSheaf C.smallEtaleTopology (ModuleCat …)).obj
  (ModuleCat.of (ULift (ZMod ell)) (ULift (ZMod ell)))`, the regular rank-one module.
- R^q f_*: `DerivedCategory.Plus.singleFunctor … 0`, then the recorded
  `rightDerivedLowerStarPlus`, then `DerivedCategory.Plus.homologyFunctor … (q : ℤ)`.
- Constructible as modules: `Scheme.IsConstructibleEtaleModuleSheaf` applied to this
  module-valued higher direct image. This is the landed finite stratification definition,
  with finite locally constant module values on every stratum, not merely finite stalks.
- No invertibility: there is no unit or characteristic condition in the signature.

Dependency declarations read and used:
- Mathlib.AlgebraicGeometry.Noetherian: AlgebraicGeometry.IsLocallyNoetherian;
  IsNoetherian is the locally Noetherian plus CompactSpace conjunction.
- Mathlib.AlgebraicGeometry.Morphisms.Proper: AlgebraicGeometry.IsProper.
- Mathlib.AlgebraicGeometry.Morphisms.Smooth: AlgebraicGeometry.Smooth.
- Mathlib.AlgebraicGeometry.Geometrically.Connected: AlgebraicGeometry.GeometricallyConnected,
  the connected member of the recorded geometrically-irreducible definition node's matches.
- Mathlib.Topology.KrullDimension: topologicalKrullDim.
- Mathlib.CategoryTheory.Sites.ConstantSheaf: CategoryTheory.constantSheaf.
- WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs: AlgebraicGeometry.Etale.lowerStar.
  The secondary recorded declaration AlgebraicGeometry.Etale.rightDerivedLowerStarPlus is
  physically in WeilConjectures.SixFunctors.Etale.Derived.UpperLowerStarCoherence, also imported;
  its full signature and coefficient universe assumptions were read there.
- Sheaf.AlgebraicGeometry.IsConstructibleEtaleModuleSheaf:
  AlgebraicGeometry.Scheme.IsConstructibleEtaleModuleSheaf.
- The scheme-conventions dependency fixes no declaration; its component meanings are used
  above. Proof-dependency modules with recorded declarations are imported without `public`,
  except those already public statement imports. No new notions or dependency copies.

Edge cases checked: empty S is allowed, with the fibre conditions vacuous and the unique
sheaf constructible by the empty stratification; empty C over a nonempty S is excluded by
geometric connectedness, as the node requires. Degree zero, degree one, and degrees at
least two are all included. Every prime includes 2 and primes equal to a residue
characteristic, as required by the Artin–Schreier case. Neither 0 nor 1 is a prime.
Nilpotents on S and mixed characteristic are allowed. Universes are explicit: schemes
in u, coefficient ring and module carriers in u+1; ULift only transports the same finite
field and does not alter its arithmetic or the allowed schemes.

Searches for an existing statement:
- msearch leansearch: "prime coefficient higher direct image smooth proper curves constructible";
  service unavailable (Internal Server Error), recorded without a no-match claim.
- msearch leanfinder: "Higher direct images of the constant prime field sheaf in proper smooth
  curve families are constructible"; 8 hits concerning affine transition limits, constructible
  images of scheme morphisms, and module categories; no matching theorem.
- msearch loogle: `"constructible", "sheaf"`; 0 hits.
- msearch grep: `proper.*smooth.*constructible|constructible.*smooth.*proper`; 0 hits.
- rg of the same expression and the exact blueprint id in WeilConjectures and lean/Sheaf:
  only the consumer ProperSmoothCurvesFiniteModule's proof docstring mentions the item.
  That consumer allows any finite module and dimension at most one, so is a different node
  whose proof uses this theorem; it is not a duplicate of this signature.
- rg of the chosen declaration name in Mathlib/project upstream-name inventory and project
  sources: no existing declaration. No helper definition was introduced.

No statement dispute or node fault was found. Compilation and dry-run results are recorded
below after verification. The independent second reading remains the next worker's task.

Validation: scompile.py completed successfully with exit code 0 and no warnings or errors.
The delivered module compiled in 3.1 seconds; every imported module also met its 60-second
file limit. The first compile caught an incorrect ULift import path, repaired to
Mathlib.Algebra.Field.ULift before the successful compile.


## Second reading by NG

Independent second reader: read the node, its nine statement dependencies and their
recorded interfaces, the delivered Lean, and Stacks more-etale.tex 0GKV,
lemma-proper-smooth-family-curves, including the reduction paragraph preceding the
Noetherian argument. The source proves a more general base case too; this node
explicitly isolates its Noetherian case. No statement correction is warranted.

Object, hypothesis and conclusion checklist (all pass):

- Schemes C and S: `{C S : Scheme.{u}}`, with `universe u` explicitly bound.
- Noetherian S: `[IsLocallyNoetherian S] [CompactSpace S]`. Read Mathlib
  Noetherian.lean:280: these are precisely the fields of `IsNoetherian S`.
  No affineness, reducedness, field base or separation of S is added.
- Scheme morphism f: `(f : C ⟶ S)`, with precisely `[IsProper f] [Smooth f]`.
  Read their Mathlib classes: properness is separated, universally closed and
  locally finite type; universally closed gives quasi-compactness, recovering
  finite type. Smoothness is smoothness on affine ring maps, the recorded notion.
- Nonempty geometrically connected fibres: `[GeometricallyConnected f]`.
  Read Connected.lean:40 and Basic.lean:46: every field-valued base change is a
  `ConnectedSpace`, including nonemptiness. The residue-field fibre restriction
  and its further field extensions give exactly the stated geometric fibres.
  It adds no irreducibility requirement.
- Dimension exactly one: `h_dim : ∀ s : S, topologicalKrullDim (f.fiber s) = 1`.
  Read `topologicalKrullDim`: chains of irreducible closed subsets, with empty
  dimension bottom. Finite-type fibres over fields have dimension unchanged by
  field extension, so the residue-field form matches geometric fibre dimension.
- Each prime ell: `(ell : ℕ) [Fact ell.Prime]`. Its coefficient ring is
  `ULift.{u + 1} (ZMod ell)`, the same prime field transported in size.
- Every q >= 0: `(q : ℕ)`, with its integer degree `(q : ℤ)`. The order of
  parameters allows every prime and every nonnegative degree for each family.
- Constant prime-field module: `constantSheaf ...` applied to
  `ModuleCat.of (ULift (ZMod ell)) (ULift (ZMod ell))`, the regular rank-one
  module, not an arbitrary finite coefficient module. Read the Mathlib
  definition: sheafification of the constant presheaf.
- Higher direct image: degree-zero `DerivedCategory.Plus.singleFunctor`, followed
  by `rightDerivedLowerStarPlus`, then `DerivedCategory.Plus.homologyFunctor`.
  Read lowerStar in UpperLowerStar.Defs and the derived declaration in
  Derived.UpperLowerStarCoherence: objectwise etale base-change pushforward and
  its bounded-below right derived functor, with the coefficient categories used
  here. These are the direct-image node's recorded declarations.
- Constructible module conclusion: `Scheme.IsConstructibleEtaleModuleSheaf` of
  precisely that higher direct image. Opened its full definition and
  `LocallyClosedStratification`: finite locally closed partition, immersions
  realizing the parts, constructible parts and etale constant module charts
  with finite values. It is not merely a finite-stalk assertion.
- No invertibility of ell: no characteristic, unit, or invertible-exponent
  hypothesis occurs. The source's cases (a) and (b) are both included.

Edge cases: empty S is allowed and the zero-stratum partition is allowed by the
constructibility definition. Empty C over nonempty S is excluded by connected
geometric fibres, as required. Degree zero and all positive degrees are included;
no claim is lost at q=0. Prime 2 and primes equal to residue characteristics are
included; ell=0 and ell=1 are correctly excluded by primality. Mixed characteristic
and nonreduced bases are allowed. There is no index-set parameter. Scheme size u
is arbitrary; finite prime-field coefficients lift to the established u+1 module
universe, imposing no equality between object and morphism site universes. All
signature variables and universes are bound.

Independent duplicate searches:

- LeanFinder via msearch: "constructibility of higher pushforwards of constant
  Z/p sheaves on smooth proper relative curves": eight hits, concerning
  constructible images and structure-module pushforwards, no matching statement.
- Loogle via msearch: `"constructible", "constantSheaf"`: zero hits.
- LeanSearch via msearch: "Higher direct images of constant finite prime fields
  for smooth proper families of geometrically connected curves are
  constructible": unavailable (Internal Server Error); no negative verdict.
- rg in Mathlib, upstream WeilConjectures and project lean/Sheaf for prime/ZMod
  with constructible, in both orders. Opened the plausible upstream hits:
  padicAlgCl compact-support finiteness uses invertible characteristic and
  different coefficients; constructibleFiniteTor_derivedDual concerns duality
  on the pro-etale site, not this theorem. Opened the project finite-module
  curve theorem: it is the distinct downstream node, with arbitrary finite
  modules and dimension at most one, and cites this item in its proof plan.
  No duplicate declaration or missing private notion was found.

No new nodes or dependency modules are delivered, so H12/H13 introduce no
additional review obligations. The single theorem has only `sorry`, no definition
or hidden data choice. Its source/blueprint docstring preserves the seven proof
steps and citations. No local notation, instance or private declaration occurs.
Checked verbatim equality of lean.statement with the file signature by Python.

Mismatches found: none. Changes: appended this independent reading only; the Lean
and node record are retained unchanged.

Second-reader validation: scompile.py exited 0 with no errors or warnings.
The delivered module compiled in 3.1 seconds; every dependency also met its
60-second per-file limit (nice 19, two threads).
