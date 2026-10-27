## Worker report

The module Sheaf.AlgebraicGeometry.UniformSectionDifferentialBound states
AlgebraicGeometry.Scheme.Hom.exists_uniform_section_differential_bound, with exactly
one postponed theorem and a real auxiliary construction sectionDifferentialModule.
The node's statement, dependencies, proof and other fields are unchanged; only lean
is recorded. No new node or dependency repair is needed.

Hypotheses and clauses, matched individually:

- R is a discrete valuation ring: `(R : Type u) [CommRing R] [IsDomain R]
  [IsDiscreteValuationRing R]`. The last class includes the local and principal-ideal
  structures and excludes fields.
- Its fraction field K: `[Field K] [Algebra R K] [IsFractionRing R K]`.
- The specified separable residue closure: `[Field ksep]`, its algebra structure over
  `IsLocalRing.ResidueField R`, and `IsSepClosure (IsLocalRing.ResidueField R) ksep`.
  `Algebra R ksep` and the scalar tower specify the composite residue-field action.
- A is the strict henselization relative to that closure: `[CommRing A] [Algebra R A]`
  and `P : Algebra.StrictHenselizationPresentationIn.{u,u} R ksep A`, the recorded
  universal pointed-etale colimit with its R-algebra identification. No henselian,
  domain or DVR assumption on A is added; these are consequences of the presentation.
- The scheme over R and its morphism: `{X : Scheme.{u}} (f : X ⟶ Spec (.of R))`.
- Flatness: `[Flat f]`.
- Finite type: `[LocallyOfFiniteType f] [QuasiCompact f]`, the recorded conjunction.
- Smooth generic fibre: `Smooth (pullback.snd f
  (Spec.map (CommRingCat.ofHom (algebraMap R K))))`. This is precisely the structure
  morphism X_K → Spec K, without a relative-dimension condition.
- Each A-valued point over R: a morphism `a : Spec (.of A) ⟶ X` with
  `a ≫ f = Spec.map (CommRingCat.ofHom (algebraMap R A))`. We quantify over these
  morphisms with that equality as an implication; no existence of such a is assumed.
- V_a: `f.sectionDifferentialModule a` applies the recorded tensorPullback functor to
  `f.relativeDifferentials` and takes its actual global sections on the top open.
  `ModuleCat.restrictScalars (Scheme.ΓSpecIso (.of A)).inv.hom` gives their canonical
  A-module structure. This helper introduces no choice, arbitrary map or proof gap.
- The torsion submodule: `Submodule.torsion A (f.sectionDifferentialModule a)`.
  Mathlib uses annihilation by a nonzerodivisor. A is a DVR, hence a domain, by the
  strict-henselization DVR result cited in the proof; thus this is exactly annihilation
  by some nonzero element as in the node. No domain assumption is imposed on A.
- The differential defect is written inline as `Module.length A` of that submodule;
  its type is ℕ∞, so infinite length is represented honestly, without truncation.
- A common nonnegative integer bound: `∃ c : ℕ, ∀ a, ... ≤ (c : ℕ∞)`. Natural numbers
  are exactly the nonnegative integers in the node. The existential occurs before a,
  so c is uniform over all sections, while R, A, P and f are fixed first.
- No equidimensionality, properness, completeness, excellence or separatedness
  hypotheses appear. No Nonempty instance or chosen section is present.
- Universe u is explicit and arbitrary. All rings and schemes are placed in one
  common universe as required by Scheme morphisms; no equality between a site's
  independent object and morphism universes is imposed. The strict henselization
  presentation indexes etale algebras in that same arbitrary universe.

Dependency declarations read and reused:

- def-sc-discrete-valuation-ring: Mathlib.RingTheory.DiscreteValuationRing.Basic,
  IsDiscreteValuationRing (full class extends IsPrincipalIdealRing and IsLocalRing).
- def-sc-ring-strict-henselization:
  Sheaf.RingTheory.StrictHenselizationPresentationIn,
  Algebra.StrictHenselizationPresentationIn, including cocone, isColimit and
  identification. The earlier presentation is publicly imported by that module.
- def-weil-pbc-module-length: Mathlib.RingTheory.Length, Module.length.
- def-pc-scheme and def-weil-affine-spectrum: Mathlib.AlgebraicGeometry.Scheme,
  AlgebraicGeometry.Scheme, Scheme.Hom, Spec and Spec.map.
- def-weil-flat-morphism: Mathlib.AlgebraicGeometry.Morphisms.Flat,
  AlgebraicGeometry.Flat (affine definition, equivalent to stalk flatness).
- def-weil-finite-type-morphism: Mathlib.AlgebraicGeometry.Morphisms.FiniteType and
  Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact, LocallyOfFiniteType and QuasiCompact.
- def-pc-base-change: WeilConjectures.AlgebraicGeometry.BaseChangeConventions;
  the node's note specifies Limits.pullback and pullback.snd for the scheme and
  its structure morphism. moduleBaseChange is the distinct module-base-change clause.
- def-sbc-smooth-morphisms: Mathlib.AlgebraicGeometry.Morphisms.Smooth, Smooth.
- def-sc-relative-differential-sheaf:
  WeilConjectures.AlgebraicGeometry.Modules.Differentials,
  AlgebraicGeometry.Scheme.Hom.relativeDifferentials.
- def-pc-module-pullback:
  Sheaf.AlgebraicGeometry.TensorPullbackSectionAdjunction publicly supplies the upstream
  AlgebraicGeometry.Scheme.Modules.tensorPullback. Only the actual tensor functor is
  needed, not a choice of adjunction or its unit.
- Torsion uses Mathlib.Algebra.Module.Torsion.Basic, Submodule.torsion and its
  membership characterization; canonical affine scalars use Scheme.ΓSpecIso.

All recorded proof-dependency modules are imported privately, alongside the relevant
Mathlib modules. lem-trf-relative-differential-sheaf-base-change has no recorded Lean
module or Mathlib match, so its import is omitted; its uses remain in the full
natural-language proof docstring. The docstring follows all ten node proof steps,
including projectivity with varying ranks, Hom denominator clearing, the uniform
annihilator, Smith generators, length estimates and the finite maximum.

Source checked: BLR Neron Models, Section 3.3, definition on printed p.65 and Proposition
3 with proof on pp.66--67. Read the primary PDF at
https://www.math.stonybrook.edu/~kamenova/homepage_files/Bosch_Raynaud_Neron_Model_tc.pdf
(PDF pages 72--74, counting from 1). Proposition 3 bounds all R^sh-points, and its proof
explicitly partitions generic components by dimension. The DAG's accepted proof is the
alternative module-theoretic argument, reproduced in the theorem docstring.

Edge cases checked before drafting: X empty or with no A-valued sections (the bound can
be zero); an empty generic fibre; smooth X (torsion zero); relative dimension zero;
a disjoint union with different generic dimensions; zero generators m and zero
annihilator exponent N in the proof. For xy = pi² the section (pi,pi) has a nonzero
length-one defect, so the formula is not accidentally free rank or total length.
No characteristic or residue-field perfection restriction appears.

Searches for existing statements and notions:

- msearch.py leanfinder, query "Uniform bound on lengths of torsion in relative
  differentials pulled back along strict henselian sections of a generically smooth
  finite type scheme over a discrete valuation ring": eight hits on inertia degree,
  standard smoothness, cotangent spaces and formal smoothness, none the uniform bound.
- msearch.py loogle, query "Module.length, Submodule.torsion,
  AlgebraicGeometry.Scheme.Hom.relativeDifferentials": no matching combined declaration.
- msearch.py leansearch, query "Uniform bound on lengths of torsion submodules of
  section pullbacks of relative differentials for a generically smooth finite type
  scheme over a discrete valuation ring": eight hits, including Submodule.torsion,
  torsion_isTorsion and standard-smooth cotangent vanishing; no uniform bound.
- msearch.py grep, query "torsion.*length|length.*torsion|uniform.*differential" under
  Mathlib/AlgebraicGeometry: zero hits.
- rg in lean/WeilConjectures and lean/Sheaf for torsion/length in either order and
  uniform differential/section defect terminology: unrelated Riemann--Roch and
  integral cohomology torsion discussions, no section differential bound. A separate
  exact-id search for lem-sfb-uniform-section-differential-bound and name searches for
  sectionDifferentialModule and exists_uniform_section_differential_bound found no
  existing declaration. Read Submodule.torsion rather than defining torsion anew.

The first scompile.py call completed with exit 0: the server's preliminary compile
reported OSError(28, 'No space left on device'), then its prescribed confirmation
against current server sources compiled this module in 2.1 s without errors or
unexpected warnings. No local build or library mutation was performed.

## Second reading by NH

Author's second reading under the dispatcher's no-subagents instruction; the maintainer
provides the independent review. Reopened the node and final Lean module and checked
every binder and conclusion again. The fraction-field smoothness is on pullback.snd;
the section condition has direction Spec A → X → Spec R; the residue-closure scalar
tower and universal strict-henselization presentation are retained. The module helper
uses the inverse of ΓSpecIso, whose source is A, as required for restriction of scalars.
The torsion is measured over A, and ℕ∞ preserves infinite lengths. The natural-number
bound is chosen before all sections, with an implication restricting them to R-maps.
The empty-section and mixed-dimension cases remain included. Every theorem proof is
sorry; the helper's data is a real functor application. No statement mismatch or
correction was found, and no dependency record was changed.
