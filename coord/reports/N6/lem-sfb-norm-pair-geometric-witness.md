## Worker report

The delivery states `AlgebraicGeometry.Scheme.Modules.norm_pair_geometric_witness` in
`Sheaf.AlgebraicGeometry.NormPairGeometricWitness`. Its only postponed theorem has the whole
proof `by sorry`. It introduces no new definition, construction, axiom, dependency record,
or statement correction. The item's JSON changes only in `lean`.

Hypotheses, matched to the node:

- The algebraically closed field is `(k : Type u) [Field k] [IsAlgClosed k]`.
- The smooth proper integral finite-type k-scheme is `(D : Scheme.{u})`, its actual
  structure morphism `f : D ⟶ Spec (.of k)`, and `[Smooth f] [IsProper f] [IsIntegral D]`.
  Properness supplies locally finite type and quasi-compactness, exactly the specified
  finite-type condition; these are not imposed again as redundant hypotheses.
- Dimension one is `hdim : topologicalKrullDim D = 1`, with the recorded topological
  dimension rather than the different local-ring dimension convention.
- A finite group of k-automorphisms is `(G : Type v) [Group G] [Finite G]`, the actual
  action `ρ : G →* Aut D`, and `hρ : ∀ g, (ρ g).hom ≫ f = f`. The group universe is
  independent of the scheme universe. No faithful-action hypothesis is added.
- The closed point is `x : D` with `hx : IsClosed ({x} : Set D)`. Its k-rationality is
  `hxr`: bijectivity of the canonical map k → Γ(D, top) → O(D,x) → κ(x). This fixes
  the base map, rather than asking for an arbitrary isomorphism of residue fields.
- Distinct orbit points are `hfree : Function.Injective (fun g ↦ (ρ g).hom x)`.
- The invertible module, positive power, and global generation are `L`, `[L.IsInvertible]`,
  `n`, `hn : 1 ≤ n`, and `Nonempty (SheafOfModules.GeneratingSections (L.tensorPow n))`.
- The section is `a : (L.tensorPow n).sections`. Its simple zero is `ha`: on every open
  neighbourhood U of x, for every free generator e and coefficient α expressing a as αe,
  the germ of α is in the maximal ideal and outside its square. `IsFreeGenerator` is
  the existing definition of a sheaf frame (unique scalar expression on every smaller
  open). Invertibility guarantees frames; the condition is not a universal quantification
  over an empty family. All local coefficients exist uniquely in a frame.
- Nonvanishing at all other orbit points is `haorbit : ∀ g, g ≠ 1 → ...`, using the
  existing residue-nonvanishing predicate `nonvanishingLocus`.

Conclusions, in their Lean conjunction order:

1. `S` is written literally as the union over g of inverse images of the complement of
   `nonvanishingLocus (L.tensorPow n) (a.val (op ⊤))`. Thus it is the node's union of
   inverse images of the residue-zero set, without a second definition of zero locus.
   The first conclusion is `S.Finite`.
2. Stability is `∀ h y, (ρ h).hom y ∈ S ↔ y ∈ S`. Since each h is an automorphism this
   is exactly hS = S, including the reverse containment.
3. For every `y ∈ S`, `IsClosed {y}` and bijectivity of the same canonical k → κ(y)
   assert that S consists of k-rational closed points.
4. `@FiniteDimensional k Γ(L.tensorPow n, ⊤) ... (Module.compHom ... )` asserts finite
   dimension of the global sections with the scalar action induced by f. Evaluation
   of a compatible global section at the terminal open canonically identifies the
   node's H with this module; conversely every section at top restricts to a compatible
   family. No noncanonical vector-space structure is quantified or assumed.
5. Properness of each evaluation kernel is expressed by `∀ y ∈ S, ∃ c, residueValue
   (c.val (op ⊤)) y trivial ≠ 0`. Evaluation is the canonical k-linear germ-then-tensor
   map into the residue fibre, so its kernel is proper if and only if some value is
   nonzero. This equivalent formulation avoids introducing a second evaluation map
   or a private kernel definition.
6. `∃ b, ∀ y ∈ S, y ∈ nonvanishingLocus ... b` is the required avoidance section.
7. The subsequent universal quantifier `∀ b, (...nonzero on S...) → ...` applies to
   every such b, not merely the chosen existential witness.
8. Both norm sections are the already defined `pencilNormSection (fun g ↦ ρ g) L n`;
   the target module is the power of the already defined `pencilOrbitBundle`. Equality
   of the complement of the first norm's nonvanishing locus with S is `Z(s) = S`.
9. `Disjoint` of the two residue-zero sets is no common zero. `Epi` of the canonical
   `freeHomEquiv.symm` for the existing `pencilSectionPair` is precisely sheaf generation
   by these two sections. Its ULift (Fin 2) index includes exactly two entries.
10. The final universal quantification over U containing x, every free generator e, and
    coefficients α, β with `s = α • e`, `t = β • e`, states that α's germ lies in m
    outside m² and β's germ is a unit. It then quantifies every local function q on
    every neighbourhood V representing the germ α times the canonical inverse of β.
    `residueValue (M := f.relativeDifferentials) (f.relativeDifferentialsDerivation.d q)
    x hxV ≠ 0` is the actual nonzero sheaf differential in the residue fibre. Every germ
    has a local representative, by `D.presheaf.exists_germ_eq`; compatibility of the
    sheaf derivation makes this formulation independent of that representative. Hence
    quantifying representatives does not lose the differential-of-the-ratio clause.
    In particular it neither substitutes algebraic differentials for the specified
    sheaf nor strengthens unitness to invertibility on the original entire U.
11. No invertibility of the group order, characteristic restriction, projectivity,
    ampleness, or other additional geometric hypothesis occurs.

Dependency declarations used:

- `Field` from Mathlib.Algebra.Field.Defs and `IsAlgClosed` from
  Mathlib.FieldTheory.IsAlgClosed.Basic (the algebraically closed part of the recorded
  algebraic-closure dependency).
- `AlgebraicGeometry.Smooth`, Mathlib.AlgebraicGeometry.Morphisms.Smooth;
  `AlgebraicGeometry.IsProper`, Mathlib.AlgebraicGeometry.Morphisms.Proper;
  `AlgebraicGeometry.IsIntegral`, Mathlib.AlgebraicGeometry.Properties;
  `AlgebraicGeometry.LocallyOfFiniteType` and `AlgebraicGeometry.QuasiCompact`, inherited
  through IsProper, from their recorded Mathlib morphism modules.
- `topologicalKrullDim`, Mathlib.Topology.KrullDimension.
- `AlgebraicGeometry.Scheme.Modules.IsInvertible` and `tensorPow`,
  WeilConjectures.AlgebraicGeometry.Modules.Invertible. This tensorPow uses the actual
  unit at exponent zero and right-associated powers at successors.
- `SheafOfModules.GeneratingSections` and `freeHomEquiv`, the recorded Mathlib generators API.
- `AlgebraicGeometry.Scheme.Modules.tensorPullbackSectionAdjunction`,
  Sheaf.AlgebraicGeometry.TensorPullbackSectionAdjunction, is the normalized pullback
  used by the norm construction; it publicly retains the existing tensorPullback.
- `SheafOfModules.cochainModulesMonoidal`,
  Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses, is retained through the
  norm module's public imports; no second tensor is supplied.
- `AlgebraicGeometry.Scheme.Modules.pencilOrbitBundle`, `pencilNormSection`, and
  `pencilSectionPair`, Sheaf.AlgebraicGeometry.AmpleCurveTwoSectionPencil. The dependency
  node owns the first two constructions and their underlying list recursion/comparisons.
- `AlgebraicGeometry.Scheme.Hom.relativeDifferentials` and
  `relativeDifferentialsDerivation`, WeilConjectures.AlgebraicGeometry.Modules.Differentials,
  construct the actual sheaf and its universal derivation; their affine description
  uses the recorded Mathlib KaehlerDifferential and its universal derivation D.
- Existing auxiliary APIs `IsFreeGenerator` (WeilConjectures.AlgebraicGeometry.Modules.FreeGenerator)
  and `residueValue` (WeilConjectures.AlgebraicGeometry.Modules.ResidueFiber) render frames
  and their fibre values, without introducing new notions.

All currently recorded proof-dependency modules are imported without `public` (statement
modules already public need no duplicate import). The Mathlib matches for finite components,
closed-point residue fields, finite linear avoidance, and localization of differentials are
also imported. The two proof-only nodes without a recorded declaration or Mathlib match,
`lem-trf-proper-field-invertible-coherent` and `lem-trf-affine-chart-stalk-differentials`,
do not supply any object needed to type this statement; no missing
statement interface is replaced by an assumption. Their mathematical steps remain in the
complete proof docstring for stage 3. No proof import creates a cycle in this new module.

Edge cases checked before and after writing:

- The trivial group is allowed: on P¹ take O(1), a=X, b=Y, with x=[0:1]. Its orbit has
  one point; both the simple-zero and differential clauses are the ordinary ones.
- Positive characteristic dividing |G| is allowed. For example, translations by F_p
  on P¹ in characteristic p give a free finite orbit in A¹. The norm polynomial
  z^p-z has derivative -1, so no separability-by-averaging assumption is appropriate.
- n=1 is included. The tensor-unit convention does not silently change this exponent.
- A trivial power on a proper integral curve has no section with a simple zero; the
  corresponding case is excluded by ha itself, not by an artificial positivity clause.
- The empty scheme is already excluded by integrality and by the supplied point x.
  Empty opens have no witness hxU or hxV. A finite group is intrinsically nonempty.
- A free orbit does not require the action globally faithful as a separate assumption.
- The possible zero section a is excluded by the actual simple-zero condition. S
  contains x, so the finite-avoidance and local-ratio conclusions are not vacuous.
- β is required to be a unit only as a germ. A large neighbourhood may contain zeros
  of β; representing its inverse on a smaller V covers exactly this case.

Searches (2026-10-24):

- msearch.py leanfinder: "A simple zero of a section on a smooth proper curve gives
  orbit norm sections without common zeros and nonzero differential". Eight hits,
  all specialized Weierstrass curve facts, no matching statement.
- msearch.py loogle: "KaehlerDifferential.D, IsUnit". Zero hits.
- msearch.py leansearch: "norm of sections line bundle on curve with simple zero no
  common zero". Eight hits: manifold frames, analytic orders, vector bundles, and
  RingedSpace.zeroLocus; none gives the norm-pair witness.
- msearch.py grep: "pencilNormSection|norm_pair_geometric|simpleZero", AlgebraicGeometry.
  Zero Mathlib hits.
- rg in lean/WeilConjectures and lean/Sheaf for the item id and `norm_pair_geometric`:
  no existing statement. Searches for simpleZero/SimpleZero, local-frame/germ, residue
  section evaluation, and differential stalk interfaces found the APIs listed above.
  The already stated ample two-section pencil gives a different existence theorem
  requiring ampleness/projectivity, with no simple-zero or nonzero-differential conclusion;
  only its canonical norm definitions and pair family are reused here.
- Read the source `literature/stacks-project/curves.tex`, lemma-uniformizer-works at
  lines 2412ff (Tag 0C1E): a uniformizer has nonzero differential in the residue fibre,
  exactly the final use of the local m/m² condition. Latest blueprint tree was searched;
  this auxiliary node's blueprint ancestor is null and its detailed argument is its
  recorded source/proof, not a separate imported unit statement.

Validation: prescribed scompile.py compiled the sandbox and library forms cleanly.
Only the expected postponed proof is present. Maximum Lean line length is 94.
No STATEMENT-DISPUTED issue or node correction was found.

## Second reading by N6

Reopened the node and final module and checked every hypothesis and conclusion in the
mapping above. This is the dispatcher's single worker's second pass, not a claim that
another agent reviewed it; the prompt forbids starting other agents and the maintainer's
independent review follows delivery.

The important interface checks were: properness already includes finite type; the dimension
is topological; rational residue fields use the canonical base map; the action preserves f;
all frames, not just a chosen frame, enter both ha and the conclusion; kernel properness is
exactly nonzero evaluation; b is both existential and universally handled; the canonical
norm comparison places s and t in B^n; generation is sheaf epi rather than sectionwise
surjectivity; and the ratio's differential is in the actual relative differential fibre.

The final clause was deliberately checked on a frame whose β has zeros away from x:
only the germ must be a unit, and the local representative q may live on a smaller
neighbourhood. This avoids adding an unintended global-unit assumption. Universal local
representatives are not vacuous since every stalk element comes from a local section.
The first compile passed. The final rereading added the available Mathlib proof imports
for finite components, residue rationality, avoidance, and differential localization;
no mathematical statement or DAG field besides lean was changed.
