## Worker report

The module `lean/Sheaf/Paper/BoundaryDerivationSquareZero.lean` states
`AlgebraicGeometry.boundary_derivation_square_zero`, with one `sorry` and no definitions.
The node's statement and all its other fields are unchanged. No new nodes or dependency
modules are needed: sheaves, sheaf morphisms, module sheaves, additive sheaf isomorphisms,
short complexes, injective resolutions, and ring actions are existing Mathlib structures.
The algebra-sheaf data are written as an explicit diagram of these structures rather than
introduced as a new bundled notion.

Hypotheses and objects, clause by clause:

- `X : Scheme.{u}` is the node's scheme, with no finiteness, separatedness, or characteristic
  condition.
- `B C : TopCat.Sheaf CommRingCat.{u} X` are O' and O. `a : X.sheaf ⟶ B` gives the O_X-algebra
  structure on O'; `a ≫ p` gives that on O. A sheaf of commutative rings with this structure
  morphism is exactly a sheaf of commutative O_X-algebras.
- `p : B ⟶ C` is the quotient ring-sheaf map. `S` is the underlying O_X-module sequence,
  and `_hS : S.ShortExact` expresses injectivity at I, exactness in the middle, and
  surjectivity onto O as SHEAVES. In particular the theorem does not require surjectivity
  on sections of every open. `S.X₁` is I.
- `eB` and `eC` identify `S.X₂` and `S.X₃` with the underlying additive sheaves of B and C.
  `_hB` and `_hC` ensure that the module actions are exactly those induced by the structure
  morphisms, not arbitrary unrelated O_X-module structures. `_hp` identifies `S.g` with p.
  Thus this is a presentation of the same algebra extension, not a different sequence.
- `_hsq` says that the product of any two local kernel sections, embedded by `S.f` and
  `eB`, is zero. This is I² = 0. The `@id` casts merely expose the commutative-ring carrier
  behind a definitionally equal underlying additive-group carrier.
- `IA`, `IB`, `IC`, `α`, `β`, `hαβ`, `_hιA`, `_hιB`, `_hH`, and `hΓ` explicitly present the
  connecting map by ANY compatible horseshoe of injective resolutions. These are choices
  for computing the stated boundary, not additional geometric hypotheses: every short
  exact module sequence admits compatible injective resolutions; its degreewise sequences
  split because IA consists of injectives, and additive global sections preserves these
  splittings, so `hΓ` exists. The assertion quantifies over all such choices. There is no
  assumed arbitrary function or arbitrary exact-sequence boundary in the signature.

Conclusions, clause by clause:

- `σ U : C(U) →+* Module.End O_X(U) I(U)` gives the O-module structure on I, including unit,
  addition, multiplication, and O_X-linearity. Its first conjunct says that multiplication
  by p(b) on I is multiplication by the lift b in B. This is the asserted factorization
  of the B action through C. The second conjunct is compatibility of this local action
  with every open restriction. Together these are an O-module SHEAF, not just a module
  on its global sections.
- `μ : C(X) →+* End I` is multiplication by global sections on the kernel module sheaf.
  Its third conjunct identifies it sectionwise with `σ` applied to the restriction of
  that global section.
- `ρ : C(X) →+* Module.End O_X(X) H¹(X,I)` gives the asserted induced C(X)-module structure
  on H¹. A ring homomorphism to module endomorphisms encodes exactly a unital module action.
  The fourth conjunct fixes `ρ f` to be `(moduleCohomology X 1).map (μ f)`, so the action
  is the induced cohomological action, not an unrelated module structure.
- `δ : C(X) →+ H¹(X,I)` is additive. The fifth conjunct fixes its value on EVERY section
  to the connecting map: identify the section using `eC.inv`, map Γ(C) into R⁰Γ(C) by
  `Functor.toRightDerivedZero`, identify R⁰Γ(C) with H⁰(Γ(IC)), apply the actual snake
  boundary `hΓ.δ 0 1 rfl`, and identify H¹(Γ(IA)) with R¹Γ(I) by the inverse of
  `InjectiveResolution.isoRightDerivedObj`. Thus δ is precisely the connecting map
  of the extension, expressed using existing declarations.
- The final conjunct is `∀ f g, δ (f * g) = ρ f (δ g) + ρ g (δ f)`, exactly
  partial(fg) = f partial(g) + g partial(f), with f and g in Γ(X,O) = H⁰(X,O).

Dependency declarations read and used:

- `def-pc-scheme`: Mathlib.AlgebraicGeometry.Scheme, `AlgebraicGeometry.Scheme` and
  `AlgebraicGeometry.Scheme.Hom`; the scheme signature and its locally affine definition
  were read in the pinned source.
- `pqf-def-cohomology`: Sheaf.Paper.PQFCohomology,
  `AlgebraicGeometry.sheafCohomologyAndHigherDirectImages`; its full signature and docstring
  were read. Its cohomology is the established
  `AlgebraicGeometry.RingedSpace.moduleCohomology` from
  Sheaf.Topology.RingedSpaceModuleCohomology. The signature uses this exact H¹ functor and
  `RingedSpace.globalSectionsFunctor`; the boundary is computed using the Mathlib
  long-exact-sequence primitives, rather than introducing another cohomology theory.
- Mathlib.CategoryTheory.Abelian.RightDerived:
  `Functor.toRightDerivedZero` and `InjectiveResolution.isoRightDerivedObj` were read with
  their signatures and docstrings. Mathlib.Algebra.Homology.HomologySequence:
  `ShortComplex.ShortExact.δ` was read; it is the snake-lemma connecting homomorphism.
  Mathlib's `SheafOfModules.toSheaf`, `SheafOfModules.evaluation`, and the sheaf/module
  carrier APIs were read to ensure the diagram refers to the actual underlying sheaves.

Source read: https://stacks.math.columbia.edu/tag/0B8S, including its entire proof. The local
literature/stacks-project/cohomology.tex is absent on this machine, so the authoritative
Stacks page was opened. Its general topological-space theorem specializes to the node's
scheme and O_X-algebra setting. The module docstring contains the node's four proof steps
and its supporting node references. No statement correction is made.

Edge cases checked mathematically before the final statement:

- I = 0: the action has zero target and δ = 0; the identity holds.
- Split dual-number extension O[ε] → O: global sections lift, so δ = 0; ordinary quotient
  multiplication on εO is exactly σ and ρ.
- Empty scheme: all section rings and groups are trivial; zero rings are allowed by
  `CommRingCat` and the ring-hom formulation, so the empty scheme is not excluded.
- Arbitrary characteristic, including 2: the equality uses addition and multiplication
  only and never divides by 2 or assumes an integer invertible.
- Nonaffine schemes and nonsurjective maps on global sections: only sheaf surjectivity
  is imposed. No lifts of f or g on all of X are assumed.
- Arbitrary universe u: the scheme, sheaf sections, and module carriers use the standard
  project universe u; no finite index set or countability restriction is introduced.

Searches for an existing statement:

- msearch leanfinder: `connecting map in cohomology is a derivation for a square zero
  extension of sheaves of rings`. Eight hits, consisting of cotangent/Jacobi-Zariski δ
  maps and universal-derivation APIs; none states a sheaf-cohomology boundary Leibniz rule.
- msearch loogle: `Functor.rightDerived, ShortComplex`. No hits; service reported unknown
  identifier Functor.rightDerived. No exact candidate was obtained.
- msearch grep: `boundary.*derivation|square.zero`, CategoryTheory/Sites. No hits.
- msearch leansearch: `cohomology boundary map derivation square zero sheaf ring extension`.
  Service unavailable (Internal Server Error), recorded as unavailable in searches.jsonl.
- rg of Mathlib, WeilConjectures, and lean/Sheaf for `boundary.*derivation`,
  `square.zero.*boundary`, and `boundary_derivation_square_zero`: no existing declaration.
  The landed AmpleSquareZeroThickening docstring mentions the application but does not
  state this theorem.
- rg of WeilConjectures for the exact node id: no declaration; rg of
  dag/lean_names_upstream.json for the theorem name and boundary/derivation pattern: no
  candidate. `tools/lean_names_upstream.py show` was also consulted.
- DAG/blueprint searches for square-zero extensions found the existing statement and its
  Cech support nodes but no duplicate formal declaration or additional missing notion.

Validation: the server compile completed cleanly (3.6 seconds), with no errors or warnings.
The only proof is `by sorry`. The required `deliver2.py --no-push` dry run printed OK:
the statement compiles and the preflight passes except for the independent second reading,
which the second reader supplies. Nothing was pushed.

## Second reading by U1

The node states the Stacks Project Cohomology Lemma 0B8S: for a scheme `X`, a
surjection of sheaves of commutative `O_X`-algebras `O' → O` with square-zero
kernel `I`, the induced `H^0(X,O)`-module on `H^1(X,I)` makes the connecting map
`∂ : H^0(X,O) → H^1(X,I)` satisfy `∂(fg) = f∂(g) + g∂(f)`.  The source is
Stacks tag 0B8S, whose hypotheses are only the topological space and square-zero
sheaf-of-rings extension; the node's scheme and `O_X`-algebra form is the stated
specialization.

The Lean renders the objects as `X : Scheme`, ring sheaves `B C`, structure maps
`a : X.sheaf ⟶ B` and `p : B ⟶ C`, and an `O_X`-module `ShortComplex S` with
`S.ShortExact`.  Isomorphisms `eB` and `eC` identify the middle and quotient
module sheaves with the underlying additive sheaves of `B` and `C`; `_hB`, `_hC`,
and `_hp` identify the actions and quotient map, while `_hsq` is the sectionwise
square-zero condition.  The conclusion supplies the local quotient action `σ`,
its global action `μ`, the induced action `ρ` on module cohomology, and the
additive connecting map `δ`, with clauses identifying restriction, cohomological
functoriality, and the Leibniz identity.  These clauses match the node item by
item, including quantifier order and the `H^1`/`H^0` carriers.

The first reading had put chosen injective resolutions and a global-sections
exactness proof among the hypotheses.  Those are implementation witnesses, not
hypotheses of 0B8S, and would weaken the statement.  I moved `IA`, `IB`, `IC`,
`α`, `β`, `hαβ`, the two augmentation equations, degreewise exactness, and `hΓ`
into an existential block in the conclusion; `δ` is still identified with the
snake boundary transported through these witnesses.  No other statement text or
proof step was changed.

Edge cases checked: `I = 0` and split dual-number extensions give zero boundary;
the empty scheme and zero rings are admitted by the sheaf and ring-hom carriers;
characteristic 2 requires no division; non-affine schemes and non-surjective
maps on global sections are allowed; and the single universe `u` covers all
scheme and sheaf objects.

Searches found no existing declaration in Mathlib, `WeilConjectures`, or `lean/Sheaf`
for this square-zero boundary derivation statement.  LeanFinder hits concern
cotangent/universal derivations only; grep and DAG searches found no duplicate.
The repaired module compiles with `scompile.py`; its only remaining proof is the
named theorem's `sorry`.
