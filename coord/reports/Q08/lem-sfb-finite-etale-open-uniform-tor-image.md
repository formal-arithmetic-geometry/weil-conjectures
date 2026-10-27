## Worker report

The module Sheaf.SixFunctors.FiniteEtaleOpenUniformTorImage states
AlgebraicGeometry.Etale.finiteEtaleOpen_uniformTorImage, with one sorry and no new definitions.
The node is unchanged except for its lean record. No statement correction, disputed statement,
new node or dependency repair is needed. The source is main-20261015,
sec-six-functors-basics/sk-thm-sf-ctf-stability/
sk-thm-sf-ctf-stability-direct-images.proof.md, paragraph (3), expanded by the node's six proof
steps. The relative dimension source was checked directly in Stacks etale-cohomology.tex,
definition-cd-f and lemma-finite-cd (Tag 0F10), clause (1).

Hypothesis and conclusion correspondence:

- The prime ell is `(ell : ℕ) [Fact ell.Prime]`. The field is `(k : Type u) [Field k]`;
  `[CharP k p]` and `_hp : 0 < p` impose precisely positive characteristic p. Primality of
  p follows from these field hypotheses, so a separate prime assumption is unnecessary.
  `_hne : ell ≠ p` is the prime-to-characteristic condition.
- The ring is `(A : Type (u + 1)) [CommRing A] [Finite A]`; `_hA` is the existence of
  `n : ℕ` with `1 ≤ n ∧ (ell : A) ^ n = 0`. This is exactly ell^n times the ring unit
  equal to zero. There is no Nontrivial A hypothesis, so the zero ring is included.
- `U X : Scheme.{u}` with `U.Over (Spec (.of k))` and `X.Over ...` are the two k-schemes.
  LocallyOfFiniteType and QuasiCompact on each structure morphism mean finite type;
  IsSeparated on each structure morphism means separated over k. These explicit binders
  are the relevant ordinary-etale part of sk-def-sfb-dc-setting's recorded convention.
- `j : U ⟶ X`, `[j.IsOver (Spec (.of k))]`, `[IsOpenImmersion j]`, `[QuasiCompact j]`
  give exactly a quasi-compact open k-immersion. QuasiSeparated j, needed for the recorded
  numerical dimension, is synthesized from the open immersion, not added as a hypothesis.
- `∃ d : ℕ, (d : ℕ∞) = j.torsionEtaleCohomologicalDimension` gives a finite nonnegative
  integer equal to cd(j), rather than merely an arbitrary bound. The equality determines
  d from j alone, even though A occurs earlier in the binders. In particular no smaller
  coefficient-dependent dimension is substituted when A is zero.
- The first conjunction quantifies over every module sheaf F and every integer q>d,
  and asserts IsZero of H^q(Rj_*(F[0])). This is the higher module direct image on the
  ordinary unbounded derived category; singleFunctor puts F in degree zero.
- `∀ (a b : ℤ), a ≤ b → ∀ L : DerivedCategoryModule A U` quantifies over all intervals
  and ordinary unbounded derived objects. `isBoundedConstructible A U L` places L in
  exactly the dependency's D^b_c, with its finite-stratification constructibility.
- `hasTorAmplitudeIn A U a b L` tests every degree-zero module sheaf, not only finite or
  constant sheaves. Its definition was read in the recorded upstream Coefficients module.
- The finite-module clause quantifies over every `M : ModuleCat.{u + 1} A` with `Finite M`.
  It asserts IsIso of the recorded `rightDerivedLowerStarProjectionMap` at L and the
  constant sheaf M_X placed in degree zero. The target uses derived inverse image of M_X;
  the existing canonical single-degree and constant inverse-image isomorphisms identify it
  with M_U. This is precisely the displayed projection map under its canonical target
  identification, not an arbitrary isomorphism. Its adjunction-mate formula was read in
  LowerStarProjection; finiteConstantProjectionMap in the proof dependency makes this
  target identification explicit and preserves invertibility.
- The last two conjunctions assert bounded constructibility of the very same Rj_*L and
  its all-module Tor amplitude `hasTorAmplitudeIn A X a (b + (d : ℤ))`.
- No separable-closedness, nonemptiness, absolute cd(k), fixed ambient dimension, finite
  projective dimension of M, or constructibility of the test sheaves is assumed.

Dependency declarations read and used (and their modules):

- sk-def-sfb-dc-setting: WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.
  BoundedConstructible, AlgebraicGeometry.ProEtale.CondensedRing.compactificationOverField;
  its note specifies explicit setting binders, used above. Its module is a non-public
  convention import; no condensed coefficients or chosen compactification enter this lemma.
- def-weil-open-immersion: Mathlib.AlgebraicGeometry.OpenImmersion,
  AlgebraicGeometry.IsOpenImmersion.
- def-weil-finite-type-morphism: Mathlib.AlgebraicGeometry.Morphisms.FiniteType,
  AlgebraicGeometry.LocallyOfFiniteType; QuasiCompact from the imported morphism API.
- def-weil-pbc-derived-categories: WeilConjectures.AlgebraicGeometry.DerivedCategories,
  the recorded DerivedCategoryModule alias, DerivedCategory.homologyFunctor and singleFunctor
  (the owning module imports WeilConjectures.SixFunctors.Etale.Derived.Coefficients).
- def-weil-pbc-direct-image: WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs,
  lowerStar, with total rightDerivedLowerStar in the existing public
  WeilConjectures.SixFunctors.Etale.Derived.UpperLowerStarCoherence interface. Both signatures
  and the bounded-below version were read; the total version is the one this node requests.
- def-weil-pbc-constructible-complexes: WeilConjectures.AlgebraicGeometry.
  BoundedConstructibleComplexes, DerivedCategory.isBoundedConstructible.
- def-kun-derived-tensor: WeilConjectures.SixFunctors.Etale.Derived.Tensor, derivedTensor,
  used within the recorded Tor predicate and projection source and target.
- def-kun-cd: Sheaf.AlgebraicGeometry.Sites.TorsionEtaleCohomologicalDimension,
  Scheme.Hom.torsionEtaleCohomologicalDimension, the infimum of nonnegative torsion bounds.
- def-kun-tor-amplitude: Sheaf.AlgebraicGeometry.EtaleTorAmplitude, with bounded intervals
  supplied by the existing DerivedCategory.hasTorAmplitudeIn in Coefficients, as its note says.
- def-kun-projection-formula-map: WeilConjectures.SixFunctors.Etale.Derived.LowerStarProjection,
  rightDerivedLowerStarProjectionMap; FlatModuleCat supplies the module pullback-flat instance.
- def-kun-constant-sheaf: Mathlib.Algebra.Homology.Additive, Functor.mapHomologicalComplex;
  for the present degree-zero objects, CategoryTheory.constantSheaf and singleFunctor give
  the same constant complex directly. The generic constant-sheaf construction and its
  sheafification docstring in Mathlib.CategoryTheory.Sites.ConstantSheaf were read.

Every recorded proof dependency module is imported non-publicly: FiniteTorsionEtaleCohomologicalDimension,
HigherDirectImageForgetComparison, FiniteConstantProjectionFormula, OpenTorBoundFiniteConstantTests,
OpenTorBoundStalkFilteredExtension, OpenDirectImageFiniteCoefficients. The numerical dimension module
is already a public statement import. The theorem docstring carries each of the node's six proof
steps with these node identifiers. No new postponed helper theorem is introduced.

Edge cases checked before writing: zero ring (only zero unital modules), zero complex, empty U,
empty X (then any U admitting j is empty), identity j (cd=0), a=b, negative endpoints and
arbitrarily negative a, and finite non-projective M over a finite nonregular ring. Every binder
admits these cases. d is a natural number and the endpoint addition casts to integers. The
coefficient universe u+1 is the recorded small-etale convention and accommodates arbitrary
finite rings and all module sheaves of the fixed universe, with arbitrary u; no independent
smaller test universe is introduced.

Searches performed through msearch.py:

- leansearch: "Etale open immersion finite coefficients derived direct image constructibility
  Tor amplitude relative cohomological dimension" returned eight hits (IsOpenImmersion,
  IsEtale and ringed-space open-immersion constructions); none gives this statement.
- leanfinder: "For a quasi compact open immersion of finite type schemes over a field, finite
  etale coefficients derived direct image preserves bounded constructible complexes and raises
  Tor amplitude by the relative torsion cohomological dimension" returned eight hits concerning
  constructible images, finite type and etale morphisms; none gives the derived conclusion.
- loogle: `"TorAmplitude", "rightDerived"` returned zero hits.
- grep: `(TorAmplitude|tor.amplitude).*(pushforward|rightDerived)|(pushforward|rightDerived).*(TorAmplitude|tor.amplitude)`
  returned zero Mathlib hits.
- rg and the prescribed node-id grep in lean/WeilConjectures and rg in lean/Sheaf found no
  declaration for this item or its chosen name. Existing related modules include
  DirectImageTorAmplitude (uses the larger 2*dimension bound and does not give the exact cd(j)
  conjunction), OpenTorBoundArbitraryField and the two Tor-test dependencies, and
  FiniteOpenDirectImageCtf (internal condensed-module coefficients, existential bound).
  These were inspected; none is the identical statement, so existing:true is inappropriate.

Validation: scompile.py Q08 lem-sfb-finite-etale-open-uniform-tor-image on the delivered module
passed both sandbox and library compilation, in 9.5 s and 7.4 s, with no reported warnings/errors.
All universes and variables are explicitly bound and autoImplicit is false.

## Second reading by Q08

A second in-session reading reopened the node and final file; the dispatcher prohibits starting
other agents, so this is a self-review, with independent maintainer review still required.
Positive characteristic, the distinct prime, the existential positive exponent and finite ring
match exactly; importantly the zero ring has not acquired a Nontrivial hypothesis. The two
separated finite-type structure maps and IsOver j preserve the original setting. The initial
existential fixes d to the numerical torsion dimension, and the all-F higher-image clause precedes
all choices of L and endpoints. In the L clause the two input predicates match D^b_c and full
Tor amplitude; the finite-M projection clause uses the canonical mate, and the two output
predicates apply to identical total derived direct images. The projection's canonical constant
pullback identification changes neither invertibility nor the map's meaning. No field-closure
assumption or restriction to finite Tor tests was introduced. Every declaration has a blueprint
source/proof docstring, and the sole theorem proof is sorry. No mismatch or correction was found.
