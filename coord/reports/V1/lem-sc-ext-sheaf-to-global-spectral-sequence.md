## Worker report

The module states `AlgebraicGeometry.exists_sheafExt_global_spectralSequence` in
`lean/Sheaf/Paper/ExtSheafToGlobalSpectralSequence.lean`. It binds a scheme `X`,
quasi-compactness as `[CompactSpace X]`, local Noetherianity, derived-category and
Ext instances, and coherent modules `F,G`. The first conjunct gives a
`CategoryTheory.SpectralSequence` in additive commutative groups and identifies
its page 2 with `RingedSpace.moduleCohomology` applied to
`AlgebraicGeometry.moduleSheafExt`; the second gives vanishing outside the first
quadrant; the third expresses convergence to the Ext abutment; the final clause
is the stated total-degree vanishing implication. The hypotheses `hF` and `hG`
render the two coherent-module hypotheses directly via
`RingedSpace.IsCoherent`.

Dependency declarations used are `AlgebraicGeometry.IsLocallyNoetherian` from
Mathlib's `Mathlib.AlgebraicGeometry.Noetherian`, `CompactSpace` from
`Mathlib.Topology.Defs.Filter`, `AlgebraicGeometry.RingedSpace.IsCoherent` from
`Sheaf.AlgebraicGeometry.Coherent`, `RingedSpace.moduleCohomology` from
`Sheaf.Topology.RingedSpaceModuleCohomology`,
`AlgebraicGeometry.moduleSheafExt` from `Sheaf.AlgebraicGeometry.SheafExt`, and
`AlgebraicGeometry.Scheme.Modules.Ext` from
`WeilConjectures.AlgebraicGeometry.Modules.Ext`.

Edge cases checked in the statement are `p=0`, `q=0`, `n=0`, and zero objects;
all are admitted by natural-number indices and the first-quadrant implication.
Searches made: `msearch.py leanfinder` for “local to global spectral sequence
sheaf Ext”; `msearch.py loogle` for “SpectralSequence SheafExt”; grep and `rg`
over Mathlib, `WeilConjectures`, and `lean/Sheaf` for `SheafExt`, spectral
sequence, and local-to-global Ext. No existing declaration states this theorem.

## Earlier second reading (a previous round; superseded)

I reread the node and the source place (Stacks Lemma 0FZ3, Tag 0BQP). The
scheme hypotheses are rendered by `CompactSpace` and `IsLocallyNoetherian`; the
coherent-module hypotheses are the two explicit `IsCoherent` binders. The page-2
clause uses the recorded `moduleSheafExt` and `moduleCohomology` declarations,
the first-quadrant clause quantifies every page and negative bidegree, and the
abutment and total-degree clauses are represented by the explicit Ext page
identifications and vanishing implication. The module compiled cleanly after
removing an unused import and wrapping long lines; no node statement or
dependency was changed.


## Second reading by V1

I read the node statement, its source (Stacks Project, Lemma 0FZ3, Tag 0FZ3, using
Cohomology Tag 0BQP), and every declaration named by `stmt_deps`.  The node introduces a
scheme `X` that is quasi-compact and locally Noetherian, coherent modules `F` and `G`, and
a first-quadrant spectral sequence with page-two terms
`H^p(X, SheafExt^q(F,G))`, abutment `Ext^{p+q}_X(F,G)`, and the stated total-degree
vanishing implication.  `CompactSpace X` and
`AlgebraicGeometry.IsLocallyNoetherian X` render the two scheme hypotheses; the two
`RingedSpace.IsCoherent` binders render coherence.  `RingedSpace.moduleCohomology`,
`AlgebraicGeometry.moduleSheafExt`, and `AlgebraicGeometry.Scheme.Modules.Ext` are the
recorded notions for the three displayed terms.

The worker's original Lean used an integer-indexed `SpectralSequence` and identified the
page `(n,0)` with the Ext abutment.  That is not convergence: an abutment is a filtered
object whose graded pieces are the stable page terms, and the `(n,0)` term need not equal
`Ext^n`.  I repaired the theorem to use Mathlib's
`E₂CohomologicalSpectralSequenceNat AddCommGrpCat` (which encodes the first quadrant),
kept the page-two isomorphism at `(p,q)`, and replaced the false row identification by
`E.AbutsTo (fun n ↦ AddCommGrpCat.of (Scheme.Modules.Ext F G n))`.  The total-degree
vanishing implication is unchanged.  No hypothesis was added or removed.

Edge cases are covered: `p,q,n,d` range over `ℕ` (including zero), zero modules are
allowed, and no nonemptiness or characteristic restriction is introduced.  I searched
Mathlib, `WeilConjectures`, and `lean/Sheaf` (including searches for `SheafExt`,
`SpectralSequence`, and `AbutsTo`); no existing theorem states this local-to-global
result.  The module and corrected node record compile cleanly with `scompile.py`.


Further checks: the local source tree does not contain the Stacks checkout, so I
obtained and read the Stacks `cohomology.tex` section-ext and `equiv.tex`
lemma-Ext-0-regular in the sandbox scratchpad. Section 0BQP assumes a ringed space
and requires bounded-below L and bounded-above K for convergence; modules in degree
zero satisfy both bounds. Regularity and a finite dimension in Lemma 0FZ3 are used
for its separate vanishing bound, not for the spectral sequence.

Clause-by-clause verdicts: X is `Scheme.{u}` (pass); quasi-compact is
`[CompactSpace X]` (pass, no Hausdorffness); locally Noetherian is
`[IsLocallyNoetherian X]` (pass); F and G are the shared module-sheaf carrier and
`hF`, `hG` assert the recorded coherence (pass). The page-two isomorphisms quantify
all `p q : ℕ` (pass). The cohomological shape on natural bidegrees is the first
quadrant, with the genuine page-dependent differential (pass: the original
`ComplexShape.up (ℤ × ℤ)` constant in r was another mismatch). The convergence
clause is now the existing slopmaster2 `SpectralSequence.AbutsTo` (pass), whose
`Abutment` fields impose F^0 = top, F^(n+1) = bottom, decreasing steps, and
cokernel graded pieces isomorphic to stable `(p,q)` terms for p+q=n. The final
`∀ d : ℕ` implication quantifies every p,q above d and every n>d (pass; natural
d covers exactly the nonnegative integers of the node). Empty schemes are not
excluded. Universes u and w are explicitly bound: I generalized the unnecessary
`HasDerivedCategory.{u}` restriction to `HasDerivedCategory.{w}`; HasExt.{u}
is the recorded small Ext encoding of the Grothendieck module category.

The dependency module readings found no unusable record: coherence is finite type
plus finite-type kernels on every open; sheaf Ext embeds F and G in degree zero
before taking cohomology of derived internal Hom; module cohomology derives module
global sections; global Ext abbreviates `Abelian.Ext` (its upstream docstring has
a stale contravariant description, but its actual signature and definition are
correct). There are no new definition nodes or dependency modules in this delivery.
I used the existing upstream convergence notion directly, added its explicit
import, removed the unused Grothendieck theorem import, added the standard header,
and expanded the docstring to the node's three proof steps with their dependencies.
The statement record is the signature verbatim, with no hidden let or local notation.

Independent searches: LeanFinder `sheaf Hom global sections Ext spectral sequence
convergence filtration` and `local to global sheaf Ext cohomology abutment` returned
sheaf cohomology and generic Ext resolution declarations, not this theorem;
Loogle `SpectralSequence.AbutsTo` returned no hits (the upstream declaration was
found by direct rg); msearch grep `local.to.global|sheafExt.*spectral` and direct rg
of Mathlib, WeilConjectures and lean/Sheaf found no duplicate theorem. No definitions
or additional proofs were introduced; the sole theorem proof remains `sorry`.
