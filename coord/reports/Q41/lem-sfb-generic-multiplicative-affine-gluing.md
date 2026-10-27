## Worker report

The module Sheaf.AlgebraicGeometry.GenericMultiplicativeAffineGluing states
AlgebraicGeometry.Scheme.existsUnique_multiplicative_affine_extension, with its
single proof `sorry`. There are no new definitions, nodes, dependency repairs,
or statement corrections. The accepted stage-1 split is unchanged; the node
copy changes only `lean`.

The previous worker ending was a stage-1 re-splitting refusal. The current
coord/brief-stage2.md §0 explicitly authorizes stage-2 recording on the reviewed
split. The live item has no Lean record and coord/queue.tsv lists stage 2.
No repair note for this item was present. This delivery uses deliver2.py.

Source read: literature/stacks-project/divisors.tex, lemma-norm-in-normal-case
(Tag 0BD3), especially the compatible affine section maps and property (1).
The node abstracts the norm's generic function into an arbitrary function F;
its six-step argument is reproduced in the theorem docstring. This abstraction
is already part of the accepted node, not a statement correction.

Hypotheses and clauses, in order:

- Integral schemes Y and Z: `{Y Z : Scheme.{u}} [IsIntegral Y] [IsIntegral Z]`.
  The schemes and their structure sheaves use exactly Mathlib's definitions.
- The morphism p and its generic-point behavior: `(p : Y ⟶ Z)` and
  `hp : p (genericPoint Y) = genericPoint Z`.
- K and L are the actual generic stalks: `Y.functionField`, `Z.functionField`,
  definitionally the stalks at `genericPoint Y`, `genericPoint Z`.
- F is an arbitrary function: `F : Y.functionField → Z.functionField`.
  No algebraic property of F is assumed.
- Positive integer d: `(d : ℕ) (hd : 1 ≤ d)`. Nonnegative natural exponents
  with this inequality encode exactly the integers at least one.
- Specified maps on every nonempty affine U: `nAffine` is indexed by U,
  `IsAffineOpen U` and `hx : genericPoint Z ∈ U`, with type
  `Γ(Y, p ⁻¹ᵁ U) →* Γ(Z, U)`. On an integral scheme, generic-point membership
  is equivalent to nonemptiness of an open: one direction gives a point;
  the other is `(genericPoint_spec Z).mem_open_set_iff U.isOpen`.
  Thus the indexing drops no nonempty affine and adds none. Proof irrelevance
  means no choice of membership proof creates additional data.
- Multiplication and 1 are exactly the laws of `→*` (MonoidHom).
  Zero and addition are not required to be preserved.
- The affine scalar identity is `hscalar`, using the canonical `p.app U`.
- The affine generic formula is `hgeneric`. Its left side is the actual
  `Z.presheaf.germ U (genericPoint Z) hx`, and its right side applies F to
  `Y.presheaf.germ (p ⁻¹ᵁ U) (genericPoint Y) ...`.
  `(congrArg (fun z : Z => z ∈ U) hp).mpr hx` transports membership to the
  inverse image and introduces no hypothesis or arbitrary map.
- Existence and uniqueness of the family are `∃! n : ∀ V : Z.Opens, ...`.
  Every open appears, without an affine or nonempty restriction on V.
- The first conjunct extends exactly `nAffine`, as an equality of monoid maps.
- The second conjunct is restriction compatibility for every inclusion
  `i : W ⟶ V` and every section b. The inverse-image restriction is
  `Y.presheaf.map ((Opens.map p.base).map i).op` and the target restriction
  is `Z.presheaf.map i.op`.
- Every n V preserves multiplication and 1 by its MonoidHom type.
- The third conjunct states `n V (p.app V a) = a ^ d` for all V and a.
- The fourth conjunct states the generic formula for every nonempty V,
  again indexed equivalently by generic-point membership. Its maps are
  the canonical germs, with inverse-image membership transported along hp.
- On the empty open, both the source and target section rings are singleton
  rings by the empty-cover sheaf axiom. The dependent family includes this
  open, hence its component is precisely the unique map of those rings.
  All its monoid/scalar/restriction identities remain included. The generic
  conjunct does not apply there. No redundant singleton clause is needed.
- No finite, surjective, normal, separated or quasi-separated hypothesis is
  imposed; no intersection is required to be affine.

Dependency declarations read and used:

- Mathlib.AlgebraicGeometry.Scheme: AlgebraicGeometry.Scheme, Scheme.Hom,
  Scheme.Hom.app and its naturality, the canonical inverse-image opens.
- Mathlib.AlgebraicGeometry.Properties: AlgebraicGeometry.IsIntegral,
  including nonemptiness and the domain condition on all nonempty opens.
- Mathlib.Topology.Sober: IsGenericPoint, genericPoint, genericPoint_spec,
  IsGenericPoint.mem_open_set_iff.
- WeilConjectures.AlgebraicGeometry.FunctionField (public import): the
  recorded module of def-sc-function-field. Its docstring explicitly delegates
  the arbitrary integral-scheme clause to Mathlib Scheme.functionField;
  its component-product definition is not needed in this integral case.
  Mathlib.AlgebraicGeometry.FunctionField supplies Scheme.functionField and
  Scheme.germToFunctionField; the latter is the same actual presheaf germ
  used here, with its membership proof packaged by a Nonempty instance.
- WeilConjectures.Topology.PresheafModuleStalkFunctor (public import): the
  recorded module of def-weil-pbc-module-stalk. Its underlying carrier and
  germ are Mathlib TopCat.Presheaf.stalk and TopCat.Presheaf.germ, which are
  the ones used here; the module-valued bundling is unnecessary for rings.
- Mathlib.AlgebraicGeometry.AffineScheme (public import): IsAffineOpen and
  Scheme.isBasis_affineOpens, the recorded affine-basis Mathlib leaf.
- Mathlib.AlgebraicGeometry.FunctionField also supplies the proof dependency
  germ_injective_of_isIntegral, Scheme.germToFunctionField_injective and
  the stalk fraction-field instances recorded by the stalk-injectivity leaf.
- Mathlib.Geometry.RingedSpace.LocallyRingedSpace (plain proof import):
  LocallyRingedSpace.Hom and inherited PresheafedSpace.Hom, with their
  sheaf maps and naturality, as recorded on the proof dependency.

Edge cases checked mathematically before writing: empty V (singleton section
rings, as above); one-point integral Z (the only opens are empty and whole);
p the identity with F(x)=x^d (multiplicative, generally not additive);
d=1 and arbitrary positive d; non-separated Z and non-affine overlaps
(the proof uses injective generic germs on arbitrary nonempty overlaps).
Integral schemes are nonempty by definition, so excluding an empty Y or Z
adds no restriction. Scheme.{u} is the ordinary ambient scheme-category size
convention already used by p; there is no independent test-object universe.
Uniqueness among the bundled monoid maps has the same content as uniqueness
among arbitrary restriction-compatible affine extensions: the latter's
monoid and scalar properties follow locally from the fixed affine maps.

Searches on 2026-10-23, all through the prescribed msearch.py or read-only rg:

- LeanFinder: "Multiplicative maps on affine sections of integral schemes with
  a common generic germ function extend uniquely to all opens". Eight hits,
  including Scheme.germToFunctionField, exists_lift_of_germInjective and
  spreading-out/power-denominator results; none is this gluing criterion.
- Loogle: "AlgebraicGeometry.Scheme.germToFunctionField,
  AlgebraicGeometry.Scheme.appToFunctionField". Unknown appToFunctionField;
  corrected query `AlgebraicGeometry.Scheme, "germToFunctionField"` gave
  germToFunctionField, its injectivity theorem and the algebraMap-germ identity.
  They provide canonical germs and injectivity, not this affine extension.
- Mathlib grep: `germToFunctionField|appToFunctionField|[Mm]ultiplicative.*[Gg]lu`
  in AlgebraicGeometry. Ten hits, all function-field and order-of-vanishing
  APIs, no match.
- LeanSearch: "Affine multiplicative section maps of integral schemes with a
  common generic stalk formula glue uniquely to all opens". Eight hits on
  sheaf section gluing, scheme morphism gluing, section extensionality and
  germ injectivity. Scheme morphism gluing is not a match for nonadditive
  multiplicative maps in the opposite direction on sections.
- rg of lean/WeilConjectures and lean/Sheaf for
  `generic.*[Mm]ultiplicative|[Mm]ultiplicative.*[Gg]lu` returned only unrelated
  generic-Galois and twisted-descent text. Exact node-id search found none.
  The new full declaration name has no hit in either source tree.

Validation: scompile.py compiled the sole delivered module in both its sandbox
and library module positions with no diagnostics. Two earlier probes exposed
an invalid membership-transport term; the final version uses the explicit
propositional equality transport above. No diagnostic commands remain.

## Second reading by Q41

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
