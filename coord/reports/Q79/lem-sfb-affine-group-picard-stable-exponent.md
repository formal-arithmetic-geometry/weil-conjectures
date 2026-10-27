## Worker report

The module Sheaf.AlgebraicGeometry.AffineGroupPicardStableExponent states
AlgebraicGeometry.affineGroup_picard_stable_exponent. Its sole proof is `sorry`.
There are no definitions, extra nodes, dependency repairs, or statement changes.
The item JSON changes only in `lean`.

Clause-by-clause correspondence:

- An algebraically closed field k: `(k : Type u) [Field k] [IsAlgClosed k]`.
- A k-group scheme G: `(G : Over (Spec (.of k))) [GrpObj G]`. The group need
  not be commutative; the internal multiplication, inverse and identity belong
  to the recorded GrpObj, rather than being unspecified maps.
- Smooth: `[Smooth G.hom]`.
- Connected: `[ConnectedSpace G.left]`, including nonemptiness.
- Affine: `[IsAffine G.left]`.
- Finite type: `[LocallyOfFiniteType G.hom] [QuasiCompact G.hom]`, the recorded
  conjunction for finite type.
- A positive integer n chosen from G alone: `∃ n : ℕ, 1 ≤ n ∧ ...`.
  A positive natural is exactly an integer at least one as used for tensor powers.
- Every field extension K/k: `∀ (K : Type u) [Field K] [Algebra k K]` inside
  the existential. No algebraic, finite, separable, perfect or algebraically
  closed assumption on K occurs.
- G_K is the scheme fibre product:
  `pullback G.hom (Spec.map (CommRingCat.ofHom (algebraMap k K)))`.
  The specified second arrow is precisely Spec K → Spec k from the extension.
- Every invertible O_(G_K)-module: `N` ranges over this pullback's `Modules`,
  followed by `N.IsInvertible → ...`.
- N to tensor power n is trivial: `Nonempty (N.tensorPow n ≅ 𝟙_ _)`.
  The tensor unit in scheme modules is the structure sheaf. `tensorPow` is
  the existing recursive sheaf tensor power from the invertible-module module;
  its zero case is irrelevant because n ≥ 1. Its positive cases agree with
  the tensor powers of def-pur-sheaf-tensor-product by associativity and the
  unit isomorphisms, without defining another tensor product.
- The same n works for every pair (K,N): both universal binders follow the
  existential n. The final Picard-group reformulation is equivalent: addition
  is tensor product and zero is the structure sheaf's isomorphism class.
  Stating that equivalent reformulation a second time would add no assertion.
- The trivial group is allowed: no nontriviality or positive dimension occurs.

Universes: u is arbitrary, and all fields and schemes live in the same ambient
scheme universe, as in the recorded Over/Spec/pullback interfaces and the
existing project field-extension statements. In particular K does not live in
an independent universe below k, which could make the universal quantifier
vacuous. The ambient universe can contain any specified family of extensions;
there is no mathematical cardinality restriction on those extensions.

Dependency declarations read and used:

- def-weil-field: `Field`, Mathlib.Algebra.Field.Defs.
- def-weil-algebraic-closure: `IsAlgClosed`,
  Mathlib.FieldTheory.IsAlgClosed.Basic (the closure construction itself is
  not needed; this node's mathlib_match explicitly records IsAlgClosed).
- def-sc-group-scheme: `CategoryTheory.GrpObj`,
  Mathlib.CategoryTheory.Monoidal.Grp, applied in Over (Spec k), with the
  scheme Cartesian structure from Mathlib.AlgebraicGeometry.Group.Abelian.
  Also read WeilConjectures.AlgebraicGeometry.GroupScheme.Defs, which documents
  exactly this specialization.
- def-sbc-smooth-morphisms: `AlgebraicGeometry.Smooth`,
  Mathlib.AlgebraicGeometry.Morphisms.Smooth.
- def-weil-connected-scheme: `ConnectedSpace`, Mathlib.Topology.Connected.Basic.
- def-weil-affine-spectrum: `AlgebraicGeometry.Spec` and `Spec.map`,
  Mathlib.AlgebraicGeometry.Scheme; affineness is `IsAffine`.
- def-weil-finite-type-morphism: `LocallyOfFiniteType` and `QuasiCompact`,
  Mathlib.AlgebraicGeometry.Morphisms.FiniteType and QuasiCompact.
- def-pc-field-extension: `Algebra` and `algebraMap`, Mathlib.Algebra.Algebra.Defs.
- def-sc-invertible-module: `Scheme.Modules.IsInvertible` and
  `Scheme.Modules.tensorPow`,
  WeilConjectures.AlgebraicGeometry.Modules.Invertible. The latter module's
  docstring identifies its tensor with sheafification of sectionwise tensor.
- def-pur-sheaf-tensor-product: public import of the recorded module
  Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses, exposing the
  existing monoidal tensor for independent site sizes. Read its
  `SheafOfModules.cochainModulesMonoidal` signature and docstring, and the
  upstream `SheafOfModules.positiveTensorPower` construction. This delivery
  uses the already available scheme-module specialization `tensorPow`.
- def-pc-fibre-product: `CategoryTheory.Limits.pullback`,
  Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback, with the existing
  scheme pullback instance.

The stated proof dependency
Sheaf.AlgebraicGeometry.CharacterPicardIsogenySequence is imported privately;
its `AlgebraicGeometry.characterPicard_isogeny_sequence` signature and its
complete proof docstring were read. The multiplicative-cover and
field-invariance proof nodes have no recorded Lean declaration in the read
checkout, so no module for either can yet be imported. They are proof inputs,
not missing notions needed to type this statement. The theorem docstring
reproduces all four accepted proof steps, including the explicit finite-group
annihilator and the calculation on the Hopf algebra for nonreduced kernels.

Edge cases checked before writing: G=1 has only trivial line bundles after
extension and allows n=1; G_a and G_m also allow n=1; the structure-sheaf line
bundle is included for every G. A group scheme here is nonempty by its unit,
and ConnectedSpace also excludes the empty scheme exactly as the dependency
states. n=0 is explicitly excluded. No characteristic assumption excludes
nonreduced isogeny kernels such as mu_p. K=k, transcendental extensions,
and imperfect extensions in positive characteristic are all admitted. No
extension hypothesis was used to trivialize the quantifier. No axiom or
existentially chosen data construction was added.

Source check: opened the primary publisher PDF
https://www.ms.u-tokyo.ac.jp/journal/pdf/jms220104.pdf, printed pp.116--119.
Brion's conventions specify smooth connected finite-type groups; Remark
2.2(v) gives splitness over an algebraically closed field; Lemma 2.3 gives
finite Picard group and invariance for every field extension; Proposition
2.5 and the paragraph following it give the asserted uniform annihilator.
Affineness supplies the linear-group hypothesis. The locally Noetherian and
separated conventions are automatic here from finite type over a field and
affineness, so they require no added hypotheses. No STATEMENT-DISPUTED fault.

Searches (msearch.py Q79 lem-sfb-affine-group-picard-stable-exponent):

- leanfinder: "A smooth connected affine algebraic group over an algebraically
  closed field has a positive exponent killing every line bundle after any
  field extension". Eight hits: standard-smooth cotangent vanishing,
  formal smoothness over perfect fields, semilocal-ring Picard triviality,
  affine-space facts, and smooth descent. None states this theorem.
- loogle: "CommRing.Pic, IsInvertible, positiveTensorPower". No hits;
  IsInvertible is not a Mathlib identifier under that unqualified name.
- loogle, refined: '"Pic", "mapAlgebra"'. Seven hits, all ring Picard
  scalar-extension constructions or their composition/exactness laws;
  none asserts bounded exponent for algebraic groups.
- grep: `Picard|positiveTensorPower|stableExponent` in AlgebraicGeometry.
  Three Weierstrass-curve documentation hits; no matching group theorem.
- leansearch: "There exists one positive integer annihilating all Picard
  groups of a connected smooth affine group over every field extension".
  Eight ring Picard definitions/triviality/functoriality results; no match.
- rg in lean/WeilConjectures and lean/Sheaf for stable exponent, uniform
  Picard, Picard exponent, and positiveTensorPower found the existing tensor
  constructions and the normal-linearization consumer, not this theorem.
- grep -rn for the exact item id in lean/WeilConjectures returned no hit.
- An additional rg for Picard field invariance/exponent in both roots found
  curve-specific Picard base-change results and consumer docstrings, not a
  duplicate of the present smooth affine group result.

Validation: scompile.py compiled this module in both its private sandbox and
library import modes, 5.7 s and 2.3 s respectively, with no errors or warnings.
Every binder is explicit; autoImplicit is disabled. The sole postponed theorem
has the matching item node and source/proof docstring.

Final author consistency check: reopened
the item statement and final module. The positive n is outside both universal
quantifiers; the base-change arrow uses algebraMap k K in the correct
contravariant direction; the invertibility condition applies to N on G_K,
and tensorPow and the tensor unit belong to that same scheme's module
category. All five geometric hypotheses (smooth, connected, affine, locally
finite type and quasi-compact), the field hypotheses and the group structure
are present. No commutativity assumption or positive-dimension restriction
was introduced, and no extra assertion was proved. No mismatch or change was
found. Per the dispatch brief, the maintainer performs the independent review;
no other agents were started.

## Second reading by Q79

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
