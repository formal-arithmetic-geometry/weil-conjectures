## Worker report

The live node was updated while this item was in progress.  I rebased to its
current statement, which explicitly requires the canonical divisibility
filtered union, rather than only an arbitrary filtered diagram.  The module
[AllowedTorsion.lean] defines the missing data and states the resulting
isomorphism with `sorry`; no definition uses `sorry`.

The module defines `allowedTorsionIntegers S` as the subtype
`{d : ℕ // 0 < d ∧ IsUnit (d : Γ(S, ⊤))}`.  Its `LE` relation is divisibility,
and the explicit `Preorder` gives the filtered index category.  It defines
`allowedTorsionSubsheaf F d` as the underlying sheaf of the categorical
kernel `kernelSubobject (d • 𝟙 F)`, exactly the sectionwise subsheaf
`F[d]`.  The lemma `allowedTorsionSubsheaf_mono` supplies the inclusion when
`d ∣ e`; its proof uses `kernelSubobject_comp_le` after writing
`(e : ℕ) • 𝟙 F = (d • 𝟙 F) ≫ (r • 𝟙 F)`.  `allowedTorsionDiagram` is the
resulting functor from the divisibility preorder, and
`allowedTorsionCocone` has point `F` and the kernel arrows as its cocone
maps.  The main statement is
`allowedTorsion_colimit_map_isIso`: for
`[Scheme.IsTorsionSheafOfInvertibleOrder S F]`, the canonical map
`colimit.desc (allowedTorsionDiagram S T F) (allowedTorsionCocone S T F)` is
`IsIso`.  This renders the node's canonical map
`\varinjlim_{d\in I_S} F[d] → F` and its isomorphism conclusion.

The first node clause uses the recorded
`AlgebraicGeometry.Smooth` notion and
`AlgebraicGeometry.smooth_iff_flat_locallyOfFinitePresentation_smooth_fiberToSpecResidueField`:
flatness, local finite presentation, and smoothness of every residue-field
fibre are exactly the stated equivalence, without a finite-type hypothesis.
The affine-space clause uses the recorded Mathlib
`AlgebraicGeometry.AffineSpace`; its upstream
`AffineSpace.smoothOfRelativeDimension_over` instance gives smoothness of
`𝔸^n_S → S` after specializing the finite coordinate type to
`ULift (Fin n)`, including `n = 0`.  The allowed-torsion hypothesis is the
canonical source class
`AlgebraicGeometry.Scheme.IsTorsionSheafOfInvertibleOrder`: for every
geometric point `Spec (.of Ω) → T` and stalk element `x`, it supplies
`0 < d`, `IsUnit (d : Γ(S, ⊤))`, and `d • x = 0`, with no common annihilator.
The global-versus-local `Spec ℤ`, `j_!(ℤ/2)` comparison is explanatory in the
node and is reflected by the global `Γ(S, ⊤)` unit condition.

Dependency declarations used (module, declaration):

- `Mathlib.AlgebraicGeometry.Scheme`, `AlgebraicGeometry.Scheme`;
  `Mathlib.AlgebraicGeometry.Morphisms.Smooth`, `AlgebraicGeometry.Smooth`;
  `WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.SmoothFiber`,
  `AlgebraicGeometry.smooth_iff_flat_locallyOfFinitePresentation_smooth_fiberToSpecResidueField`.
- `Mathlib.AlgebraicGeometry.Morphisms.Flat`, `AlgebraicGeometry.Flat`;
  Mathlib `AlgebraicGeometry.LocallyOfFinitePresentation`;
  `Mathlib.AlgebraicGeometry.Fiber`, `AlgebraicGeometry.Scheme.Hom.fiber`;
  `Mathlib.AlgebraicGeometry.ResidueField`, `AlgebraicGeometry.Scheme.residueField`.
- `WeilConjectures.AlgebraicGeometry.EtaleSheaves`,
  `AlgebraicGeometry.Scheme.IsLocallyConstantEtaleSheafOfSets` (the source
  module also supplies the sheaf-of-modules context);
  `Mathlib.FieldTheory.IsAlgClosed.Basic`, `IsAlgClosed`;
  `Mathlib.CategoryTheory.Sites.Point.Basic`,
  `CategoryTheory.GrothendieckTopology.Point.sheafFiber`.
- Mathlib `AlgebraicGeometry.AffineSpace`;
  `Mathlib.AlgebraicGeometry.Scheme`, `AlgebraicGeometry.Spec`;
  `Mathlib.AlgebraicGeometry.OpenImmersion`,
  `AlgebraicGeometry.IsOpenImmersion`;
  `Mathlib.CategoryTheory.Sites.ConstantSheaf`,
  `CategoryTheory.constantSheaf`.
- `WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Defs`,
  `AlgebraicGeometry.Etale.openImmersionLowerShriek`;
  Mathlib `CategoryTheory.sheafIsAbelian` (kernel in
  `Sheaf J AddCommGrpCat`);
  `Mathlib.CategoryTheory.Limits.HasLimits`,
  `CategoryTheory.Limits.colimit` (with `Cocone`, `IsColimit`, and
  `CategoryTheory.IsFiltered`).

The module imports the canonical upstream `WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.TorsionSheaf`, which supplies the allowed-torsion class and the sheaf/colimit infrastructure; it does not copy or redefine any recorded dependency notion.

Edge cases checked: `1` belongs to `I_S`, and products give common upper
bounds, so the divisibility preorder is filtered; `n = 0` is excluded by the
positive predicate; `n = 0` affine space is represented by `ULift (Fin 0)`;
empty stalks satisfy the elementwise condition vacuously; each stalk element
may use a different globally invertible integer; and the `Spec ℤ` example
separates global units from units only on a neighbourhood.  All universe
binders are explicit (`Λ : Type (u + 1)`, `S,T : Scheme.{u}`, and the sheaf
category `ModuleCat.{u + 1} Λ`).

Searches made: `msearch.py ... leanfinder` for the allowed-torsion filtered
union returned unrelated étale-locus declarations; `msearch.py ... loogle`
for `IsTorsionSheafOfInvertibleOrder, exists_isColimit, Smooth,
smoothOfRelativeDimension` returned no Mathlib hit for the custom names;
`msearch.py ... grep IsTorsionSheafOfInvertibleOrder AlgebraicGeometry`
returned no Mathlib hit.  `rg` in slopmaster2 found the canonical
`IsTorsionSheafOfInvertibleOrder` class and its general filtered-colimit
source theorem, and the Mathlib affine-space declaration.  `rg` in the
project found no existing `allowedTorsionIntegers`,
`allowedTorsionSubsheaf`, or `allowedTorsionDiagram` declaration.  The exact
current source was checked with
`scompile.py --source WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.TorsionSheaf`.
The new module compiles cleanly with `scompile.py`; its postponed proofs are the named lemma `allowedTorsionSubsheaf_mono`
and theorem `allowedTorsion_colimit_map_isIso`, both belonging to the node’s
explicit kernel-inclusion and filtered-union clauses. Their docstrings give
the source and natural-language proof. No theorem was proved in this packet.

Self-check of the retained packet (2026-10-17): the node copy differs from
the current shared DAG only in `lean`; its recorded main signature agrees
verbatim with the file, and its declaration list names the six declarations
in that file. Added the standard copyright header and source docstrings for
the two divisibility instances and the postponed kernel-inclusion lemma.
The canonical diagram, cocone, and main signature are unchanged.

## Second reading by Q105

I read the current node and the module independently, the current
main-20261015 blueprint section named by its source, and the Stacks source
places used by its proof. The node copy has no `statement_change`, and its
natural statement already agrees with the reviewed shared node. This packet
changes only `lean`; it makes no mathematical statement correction, adds no
node and repairs no dependency record.

Clause-by-clause list and verdict:

1. Objects: arbitrary schemes `X,Y` and a morphism `f : X ⟶ Y`.
   Smoothness means the recorded Mathlib `AlgebraicGeometry.Smooth`, not a
   new predicate. The exact existing declaration
   `AlgebraicGeometry.smooth_iff_flat_locallyOfFinitePresentation_smooth_fiberToSpecResidueField`
   quantifies over these objects and states
   `Smooth f ↔ Flat f ∧ LocallyOfFinitePresentation f ∧
   ∀ y, Smooth (f.fiberToSpecResidueField y)`.
   I opened that theorem in `WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.SmoothFiber`.
   Its `fiberToSpecResidueField` is the projection from the recorded pullback
   `f.fiber y = pullback f (Y.fromSpecResidueField y)` to
   `Spec (Y.residueField y)`. I opened the Mathlib definitions of `Smooth`,
   `Flat`, `LocallyOfFinitePresentation`, `fiber`, and `residueField`.
   Verdict: exact criterion; no quasi-compactness, finite-type, Noetherian,
   irreducibility or field hypothesis on the schemes. Reusing this existing
   theorem avoids an H4 duplicate. Added its module as a proof import.
2. Objects: schemes `S,T`, a commutative ring `Λ`, and a sheaf of `Λ`-modules
   on the small étale site of `T`. They are
   `{Λ : Type (u + 1)} [CommRing Λ] (S T : Scheme.{u})`
   and `F : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} Λ)`.
   Allowed torsion is exactly the existing
   `Scheme.IsTorsionSheafOfInvertibleOrder S F`: its field quantifies over
   every stalk element and asserts
   `∃ n : ℕ, 0 < n ∧ IsUnit (n : Γ(S, ⊤)) ∧ n • x = 0`.
   I read both the old checkout and current source via `scompile.py --source`.
   Verdict: global units, elementwise annihilators, and no map `T ⟶ S`
   or common annihilator are added. The existing API uses separably closed
   geometric points; algebraically closed points give the same étale stalk
   condition, since purely inseparable extension of a separably closed
   field leaves its small étale point unchanged. It includes the node's
   algebraically closed geometric points and excludes no mathematical case.
3. For every natural-number dimension and every base `S`, affine-space
   projection is smooth. I opened
   `AffineSpace.smoothOfRelativeDimension_over` in
   `WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.Smooth`.
   It takes a finite coordinate type `n : Type u` and any `S : Scheme.{u}`,
   and gives `SmoothOfRelativeDimension (Nat.card n) (𝔸(n; S) ↘ S)`;
   the Mathlib class includes `Smooth`.
   Specializing to `ULift.{u} (Fin n)` covers every dimension, including zero,
   for the recorded `AffineSpace` construction. Verdict: already stated
   exactly; added the module as a proof import rather than duplicate it.
4. Global/local comparison: `Spec ℤ`, the open immersion `j : D(2) ↪ Spec ℤ`,
   and `j_!` of the constant `ℤ/2ℤ` sheaf. The first packet only described
   this in the report and had no formal statement. I added the real open
   `allowedTorsionCounterexampleOpen := PrimeSpectrum.basicOpen (2 : ℤ)`
   and `allowedTorsionLocalCounterexample`, constructed with the recorded
   `Etale.openImmersionLowerShriek` and `constantSheaf` applied to the
   rank-one module over `ULift.{1} (ZMod 2)`. Its underlying additive group
   is canonically `ℤ/2ℤ`; `ULift` only meets the standard coefficient size.
   The new `allowedTorsionLocalCounterexample_properties` states both
   clauses: at each geometric point and stalk element there is an open
   neighbourhood and a positive annihilator which is a unit on that open;
   the sheaf does not satisfy the global allowed-torsion class.
   The point-membership clause uses `t (IsLocalRing.closedPoint Ω) ∈ U`,
   and the unit clause is `IsUnit (d : Γ(U.toScheme, ⊤))`.
   Verdict: the previously missing comparison is now explicitly stated,
   with its specified witness, not an arbitrary sheaf. The docstring gives
   node proof step 6: stalk `ℤ/2ℤ` on `D(2)`, zero outside, annihilators `2`
   and `1` locally, and failure at a generic geometric point because the
   only positive unit of `Γ(Spec ℤ, O) = ℤ` is `1`.
5. Index objects and arrows: `allowedTorsionIntegers S` is precisely
   `{d : ℕ // 0 < d ∧ IsUnit (d : Γ(S, ⊤))}`. Its `LE` and `Preorder`
   instances give `d ≤ e` iff `d.1 ∣ e.1`. Verdict: exact, small index type.
   The packet described filteredness but did not state it. I added
   `@[instance] theorem allowedTorsionIntegers_isFiltered (S : Scheme.{u}) :
   IsFiltered (allowedTorsionIntegers S)` with proof postponed and the
   complete argument in its docstring: `1`, product upper bounds, and thinness.
6. Kernel subsheaves, restrictions and transition inclusions:
   `allowedTorsionSubsheaf F d` is the underlying object of
   `kernelSubobject (d • 𝟙 F)`. Sheaf kernels are sectionwise kernels, and
   module kernels have the restricted scalar action; hence this is the
   canonical `F[d]`, up to the canonical kernel representation.
   `allowedTorsionSubsheaf_mono F h` gives the subobject inequality for
   `h : d ∣ e`; `allowedTorsionDiagram` applies `Subobject.underlying`
   to that monotone family. Thus its objects are definitionally those of
   `allowedTorsionSubsheaf`, and its maps are the canonical inclusions,
   with the composition laws supplied by the subobject functor.
   `allowedTorsionCocone` has point `F` and the kernel arrows as components.
   Verdict: no arbitrary maps or independently chosen subobjects.
7. Under the sole hypothesis `[Scheme.IsTorsionSheafOfInvertibleOrder S F]`,
   `allowedTorsion_colimit_map_isIso` asserts
   `IsIso (colimit.desc (allowedTorsionDiagram S T F)
     (allowedTorsionCocone S T F))` in the category of module sheaves.
   Verdict: it identifies the specified canonical restricted colimit map,
   not merely the existence of some filtered presentation. I retained
   this main signature verbatim and checked its literal equality with
   `lean.statement`. Expanded its proof docstring into node steps 3--5:
   sectionwise kernels and module structure; divisibility and filteredness;
   construction of the canonical map; monicity by exact filtered colimits
   and the connected constant diagram; surjectivity by exact kernel
   stalks; conservativity; and module-linearity of the inverse.

Source and dependency checks: Stacks `morphisms.tex`,
`lemma-smooth-flat-smooth-fibres` (01V8),
`lemma-base-change-smooth` (01VB),
`lemma-smooth-locally-finite-presentation` (01VE), and
`lemma-smooth-flat` (01VF) concern arbitrary scheme morphisms;
no finite-type condition is imposed throughout. In `sites-modules.tex`,
`lemma-abelian` (03DA), `lemma-limits-colimits` (03DB), and
`lemma-limits-colimits-abelian-sheaves` (03CO) give the precise kernel,
colimit and exactness facts used. In `etale-cohomology.tex`,
`lemma-stalk-exact` (03PT), `theorem-exactness-stalks` (03PU), and
`proposition-describe-jshriek` (03S5) supply the stalk calculations and
conservativity, without Noetherian or finiteness assumptions. I opened the
recorded geometric-point, sheaf-fiber, constant-sheaf and open-immersion
interfaces, the affine-space instance, the extension-by-zero definition
and both of its stalk declarations, and the geometric-stalk conservativity
signature. I read the current `ModuleSheavesColimitsForgetful` and
`ConstantSheafGeometricStalk` sources through the source wrapper where
those files were absent in the older checkout. Added the stated proof
modules as ordinary imports; definitions used by the example are public
imports. No dependency notion is redefined.

Edge cases: `I_S` never has an empty index set because `1` always belongs;
`d = 0` is excluded exactly by the node's positivity requirement, whereas
affine-space dimension `n = 0` is included. If `S = Spec ℤ`, then `I_S` is
`{1}` and an allowed sheaf is zero. If `S` is empty, its global-section
ring is the zero ring, all positive integers are units, and the statement
becomes the usual torsion union. The zero sheaf and empty `T` are included.
No characteristic restriction or map between `S` and `T` is assumed. The
arbitrary universe `u` and the module category in `u+1` are the recorded
six-functor convention; they do not force an equality between site object
and morphism universes. The index subtype is in `Type 0`, so it does not
introduce an oversized limit shape. The counterexample has the intended
specific small scheme `Spec ℤ`; its lifted coefficient ring changes no
algebraic content.

Independent searches (2026-10-17): `msearch.py` LeanFinder query
"A sheaf is the directed union of its n torsion kernels indexed by positive
natural numbers invertible on the base scheme" returned eight results
about vanishing of sections and localizations, none the canonical diagram.
Loogle query `CategoryTheory.IsFiltered, CategoryTheory.Limits.kernelSubobject`
returned zero hits. The Mathlib grep query
`torsion.*kernel|kernel.*torsion|IsTorsion.*Invertible` under
`AlgebraicGeometry` returned zero hits. LeanSearch query for the extension
by zero of the constant Z/2 sheaf from D(2) in Spec Z returned eight module
torsion/localization results, none this example. Direct `rg` on the full
upstream source, Mathlib and project found the existing allowed-torsion
class and the weaker existential filtered-presentation theorem, which I
opened: its diagram is arbitrary in its signature, so it does not give
this node's specified canonical divisibility map. The all-integers
`PositiveNat` kernel diagram in `TorsionEtaleSheaf`/`PullbackIsoTorsionColimit`
is abelian-valued and allows every positive integer; it does not impose
global invertibility on arbitrary `S`. Exact-name searches across
upstream, Mathlib, project and `dag/lean_names_upstream.json` found no
collisions for the new declarations, including the counterexample and
filteredness theorem.

Changes: added the missing filteredness statement and actual global/local
counterexample; expanded the colimit proof docstring; added the dependency
proof imports and explanatory module documentation; recorded the added
declarations. The original canonical constructions and main theorem
signature are unchanged. Every new theorem, including the instance
 theorem, has proof `sorry`; definitions have concrete data and no sorry
proofs embedded in them. There are no local instances, private notions,
unbound variables, or lines over 100 characters. Compilation with the
prescribed `scompile.py Q105 sk-def-smooth
lean/Sheaf/AlgebraicGeometry/AllowedTorsion.lean` completed cleanly (sandbox
3.5 seconds, library 4.0 seconds), with no errors or unexpected warnings.
