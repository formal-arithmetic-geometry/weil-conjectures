## Worker report

The module `Sheaf.AlgebraicGeometry.MonoidSpectrumHomUniversal` states
`AlgebraicGeometry.Monoscheme.spectrum_hom_universal`, with its sole theorem proof
`sorry`. The two real helper definitions `fractionSection` and `fractionGerm` name
the canonical fraction in the already recorded spectrum presheaf and its image in
the actual sheaf stalk. They are part of this node's fraction formula, rather than
new mathematical notions. Both carry this node's blueprint/source docstrings.
The natural-language statement and proof plan are unchanged. The landed definition
node `def-trf-monoscheme-toric-realization` is added to `stmt_deps` as required by
the H2 return. No new nodes or dependency modules are needed.

Hypotheses and clauses, in order:

* A commutative monoid is `(P : Type u) [CommMonoid P]`. The node's fineness and
  integrality are exactly `(hP : FineFan.IsFine P)`: the dependency defines this as
  finite generation and injectivity into `Algebra.GrothendieckGroup P`. The source
  is additive; the library's multiplicative notation replaces zero by one,
  addition by multiplication and `p - a` by `p * a⁻¹` in the completion.
* The arbitrary topological space with its commutative-monoid sheaf is
  `T : SheafedSpace CommMonCat.{u}`. Its presheaf and sheaf condition are bundled;
  there is no fineness, integrality, sharpness or torsion restriction on its stalks.
  The common universe can be chosen to contain any given monoid, space and sheaf.
* The ordinary unsharpened target is `Monoscheme.affine P`, whose carrier is
  `FineFan.MonoidPrime P` and whose sheaf is `FineFan.spectrumSheaf P`.
  This is distinct from the sharp model `FineFan.affine P`.
* The required continuous map and restriction-compatible section homomorphisms
  are the underlying sheafed-space morphism `f : T ⟶ affine P`. Stalk locality
  is the subtype condition `FineFan.IsLocalMorphism f`, which means `IsLocalHom`
  for each actual `FineFan.stalkMap f t`.
* The bijection is `Function.Bijective` of the map on local morphisms sending f
  to `(SheafedSpace.Γ.map f.val.op).hom.comp (affineSection P)`. This is the actual
  global-sections map composed with the canonical numerator map, including the
  top-open transport. It is written directly, without `affinePullback`.
* Naturality in the source is the second conjunct, for any local `k : T' ⟶ T`:
  `(SheafedSpace.Γ.map (k.val ≫ f.val).op).hom.comp (affineSection P)` equals
  `(SheafedSpace.Γ.map k.val.op).hom.comp
  ((SheafedSpace.Γ.map f.val.op).hom.comp (affineSection P))`.
* Naturality in the fine monoid is the third conjunct. For any fine `Q` and any
  `w : P →* Q`, the unique local `g : affine Q ⟶ affine P` is characterized by
  `(SheafedSpace.Γ.map g.val.op).hom.comp (affineSection P) =
  (affineSection Q).comp w`. For every local map `f` into `affine Q`, the formula
  equates `(SheafedSpace.Γ.map (f.val ≫ g.val).op).hom.comp (affineSection P)` with
  `((SheafedSpace.Γ.map f.val.op).hom.comp (affineSection Q)).comp w`.
  The uniqueness also expresses the canonical choice of the spectrum map and
  implies its identity/composition laws, just as in the proof dependency.
* The last conjunct fixes arbitrary `ρ`, any local `f` with
  `(SheafedSpace.Γ.map f.val.op).hom.comp (affineSection P) = ρ`, and gives the
  point formula elementwise: `p ∈ (f.val.hom.base t).carrier ↔
  ¬ IsUnit (FineFan.germ T.presheaf ⊤ t (by trivial) (ρ p))`.
  Since the first conjunct supplies exactly one such `f`, this describes the
  morphism corresponding to every `ρ`, rather than assuming its existence.
* The stalk formula applies for every `p a : P` and
  `ha : a ∉ (f.val.hom.base t).carrier`. The canonical fraction germ is
  `fractionGerm (f.val.hom.base t) p a ha`: start with the constant fraction
  `GrothendieckGroup.of p * (GrothendieckGroup.of a)⁻¹` on `D(a)`, apply the
  sheafification unit, and take its actual germ. Membership in each face
  localization is constructed directly with numerator `p` and denominator `a`.
  For any unit `v` whose value is the germ of `ρ a`, the formula sends this
  fraction germ by `FineFan.stalkMap f.val t` to the germ of `ρ p` multiplied by
  the value of `v⁻¹`. The preceding point formula guarantees that such `v` exists;
  the inverse value is independent of the representing unit. This spells out
  subtraction of the denominator unit without imposing a group structure or
  cancellation on the target stalk. It is the localized stalk formula in the
  node, expressed on the actual germs representing every fraction.
* No sharpness or torsion-freeness assumption appears anywhere.

Dependencies read and used:

* `Sheaf.AlgebraicGeometry.FineFanBlowup` (statement dependency
  `def-trf-fine-fan-blowup`): `FineFan.IsFine`, `FineFan.MonoidPrime`,
  `FineFan.basicOpen`, `FineFan.spectrumSections`, `FineFan.spectrumPresheaf`,
  `FineFan.spectrumSheaf`, `FineFan.germ`, `FineFan.stalk`,
  `FineFan.stalkMap`, `FineFan.IsLocalMorphism`.
* `Sheaf.AlgebraicGeometry.MonoschemeToricRealization` (landed definition node
  `def-trf-monoscheme-toric-realization`, now explicitly in `stmt_deps`):
  `Monoscheme.affine`, `Monoscheme.affineSection`, and its unsharpened
  `Monoscheme.affineGerm` (the latter read to check the numerator convention).
* The recorded proof dependency `lem-trf-affine-monoscheme-hom-universal` was
  read in `Sheaf.AlgebraicGeometry.AffineMonoschemeHomUniversal`, including the
  full signature of `Monoscheme.affine_hom_universal` and body of its helper
  `Monoscheme.affinePullback`. The return explicitly requests dropping this
  module's import; the repaired statement writes its helper's body directly in
  every occurrence. The proof plan still cites the theorem, which is unchanged.
  The present theorem additionally states the point and fraction computations,
  so the old theorem alone is not an exact `existing: true` match.
* `lem-trf-monoid-prime-minimal-neighborhood` was read in full. It has no Lean
  record or Mathlib match on the base, so there is no recorded proof module to
  import. Its role in the accepted proof is included explicitly in the docstring.
  No extra assertion of that node is required to type this statement.

Source check: read ILO Exposé VIII 3.1.2--3.1.8, printed pp.98--99, with `pdftotext`.
In particular 3.1.6 specifies local stalk maps, and the proof of 3.1.8(i) constructs
exactly the inverse image of nonunits and the localized map. The source is more
general in P; this node explicitly restricts to fine integral P, preserved here.

Edge cases checked mathematically before writing:

* Empty `T`: no stalk or point conditions; its global-section monoid is terminal,
  so both Hom sets are singletons. No nonempty hypothesis was added.
* Trivial `P`, and `P` a group such as a finite torsion group: the unique prime
  is empty, all denominator germs are units, and the formula is a group fraction.
  Thus sharpness and torsion-freeness must not be added.
* Free rank-one monoid: the point is the empty prime when the generator germ is
  a unit and the nonunit prime otherwise. The point formula has the correct sign.
* `a = 1` (additive zero): `D(a)` is the whole spectrum and the formula is the
  numerator germ, with inverse of the identity. `p = 1` gives a denominator inverse.
* Nonintegral or nonsharp target stalks: units still have unique inverses, so the
  formula needs no subtraction operation on the ambient monoid and no cancellation.
* The denominator condition makes `D(a)` a genuine neighborhood of the point;
  no empty-open germ is formed.

Searches for reuse (2026-10-24):

* `msearch.py ... leanfinder` with query “Local morphisms to the unsharpened
  spectrum of a fine commutative monoid correspond naturally to global sections;
  the point prime is nonunit germs and stalk maps send fractions to quotients
  of germs.” Eight results, all commutative-ring spectrum interfaces, including
  `StructureSheaf.localizationToStalk_mk'`, `StructureSheaf.toStalk`,
  `LocallyRingedSpace.toΓSpec` and `LocallyRingedSpace.toΓSpecFun`.
  Their signatures require commutative rings/locally ringed spaces, so do not match.
* `msearch.py ... loogle '"MonoidSpectrum", "MonoidalSpace"'`: zero results.
* `msearch.py ... grep 'MonoidSpectrum|MonoidalSpace|monoscheme|fractionGerm'`:
  zero Mathlib results.
* `rg` of `lean/WeilConjectures` for `MonoidSpectrum|MonoidalSpace|monoscheme|
  fractionGerm|affinePullback` finds only unrelated scheme pullback modules;
  `grep -rn` of this node id there finds none.
* `rg` of `lean/Sheaf/AlgebraicGeometry` found the sharp fan universal property
  and the unsharpened `AffineMonoschemeHomUniversal` discussed above. The exact
  new helper/declaration names were absent from the project and upstream names.
  Read the full relevant definitions and docstrings, including the actual
  fraction-presheaf and sheafification construction rather than using only names.
* The prescribed `scompile.py --source` confirms the live affine-universal source
  is still a non-module file; no live `MonoidSpectrumHomUniversal` module exists.

Validation: the repaired file passes the prescribed `scompile.py` in both sandbox
and library invocations with no errors or unexpected warnings. The wrapper reported
506.6 s including server/slot waiting for the sandbox and 8.3 s for the library;
no timeout limit was changed. The original successful compilation was for returned
head `4b0329d86152`; the repair is a substantive change described below. The dry
run and delivery are rerun through the prescribed wrappers.

No `STATEMENT-DISPUTED` or mathematical node fault was found.

## Second reading by Q42

The dispatcher explicitly prohibits starting other agents, so this section records
a separate second pass by the same worker; the maintainer's independent review is
still required. Reopened the node and Lean file and checked each binder and each
conjunct: fine integral P, arbitrary monoid sheaf T, unsharpened affine space,
local stalk maps, canonical pullback bijection, both naturalities, nonunit point
prime, and the fraction computation all match. The helper's denominator belongs
to the complementary-face closure because the point is in `D(a)`; its numerator
is exactly p, with one inverse of a, not a higher power or a sharp quotient.
The unit quantifier in the last clause is not a new hypothesis on T: its existence
follows from the immediately preceding prime formula and `ha`, and its inverse
is unique. The first three conjuncts agree with the existing universal-property
theorem's full signature. No missing sharpness hypothesis is imported from the
nearby sharp-fan theorem. No corrections to the statement were necessary.

## Returned delivery repair: H2

The immutable head reviewed was `4b0329d86152`. Compared the retained sandbox node
with the current shared main-branch node: before repair only `lean` differed;
after repair only `lean` and the authorized `stmt_deps` addition differ. The
wrapper rebuilds the delivery on the current main branch.

1. Added the already landed definition node `def-trf-monoscheme-toric-realization`
   to `stmt_deps`. Read its recorded module and the full `Monoscheme.affine` and
   `Monoscheme.affineSection` definitions and docstrings. They provide exactly
   the unsharpened affine object and numerator sections used by this statement.
2. Inlined `(SheafedSpace.Γ.map f.val.op).hom.comp (affineSection P)` at each
   former `affinePullback` occurrence, with the corresponding composite morphism
   and with `affineSection Q` for a map into `affine Q`. No helper definition
   from a proof theorem's module remains in the statement.
3. Dropped `import Sheaf.AlgebraicGeometry.AffineMonoschemeHomUniversal`, exactly
   as requested. The mathematical proof plan and its theorem citation remain.
4. Re-extracted `lean.statement` verbatim from the repaired Lean signature and
   refreshed `lean.date`. All mathematical binders and all clauses, including
   the fraction formula and unrestricted target stalks, are preserved.

Second pass for the repair: checked all pullback expressions individually,
including the P-to-Q naturality where the right-hand numerator section must be
`affineSection Q`. Confirmed the new dependency already exists and is landed,
and the changes in the item node are confined to `stmt_deps` and `lean`. The
maintainer's mathematical approval of the other clauses remains applicable.
