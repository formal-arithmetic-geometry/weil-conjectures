## Worker report

The module `Sheaf.AlgebraicGeometry.FibreProductPointResidueField` states
`AlgebraicGeometry.Scheme.Pullback.exists_residueField_equiv_ofPointTensor`, with a single
`sorry` and no new definitions or nodes. It states both the residue-field isomorphism and
the field-quotient consequence, including compatibility with each factor field.

Hypothesis and clause correspondence:
- Schemes X, Y, S: `{X Y S : Scheme.{u}}`, with the universe explicitly declared.
- Scheme morphisms f and g to the same base: `(f : X ⟶ S) (g : Y ⟶ S)`.
- The point z in the chosen fibre product: `(z : ↑(pullback f g))`.
- x = p(z), y = q(z), s = f(x) = g(y): `T := Triplet.ofPoint z` is precisely this
  triple with its two equality proofs. `T.tensor` is the recorded Mathlib pushout model
  of κ(x) tensor over κ(s) κ(y), not a private tensor construction.
- The canonical tensor map ψ induced by the projections: `(ofPointTensor z).hom`.
  Its definition is `pushout.desc` of the two projection residue-field maps.
- The prime p is the kernel of that map: `p := RingHom.ker ψ`; the `letI` uses
  Mathlib's `RingHom.ker_isPrime ψ`, not an extra hypothesis or postponed proof.
- κ(p), the fraction field of the quotient: `p.ResidueField`. Mathlib supplies the
  `IsFractionRing (T.tensor ⧸ p) p.ResidueField` instance in
  `Mathlib.RingTheory.LocalRing.ResidueField.Ideal`.
- The induced map is an isomorphism: the first existential gives the ring equivalence
  `e : p.ResidueField ≃+* (pullback f g).residueField z`, with
  `e.toRingHom.comp (algebraMap T.tensor p.ResidueField) = ψ`.
  This extension equation characterizes the induced map uniquely by
  `Ideal.ResidueField.ringHom_ext`, so the existential does not merely assert an
  unrelated abstract isomorphism.
- Compatibility with κ(x) and κ(y): the next two equalities compose the canonical map
  with `T.tensorInl.hom` and `T.tensorInr.hom` and equate their images under e to
  `(pullback.fst f g).residueFieldMap z` and `(pullback.snd f g).residueFieldMap z`.
- If the quotient is a field: `IsField (T.tensor ⧸ p) → ...` is a property, so it
  does not require a chosen field structure or add a maximality assumption.
- The quotient-to-κ(z) map is an isomorphism of extensions of both factor fields:
  the second existential is a ring equivalence on `T.tensor ⧸ p`, and its three
  equations use `Ideal.Quotient.mk p` to characterize the induced map and its
  compatibility with both factor inclusions.

Dependency declarations read and used:
- def-pc-scheme: Mathlib.AlgebraicGeometry.Scheme, `AlgebraicGeometry.Scheme` and
  `Scheme.Hom`, with their signatures and docstrings read.
- def-pc-fibre-product: Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback,
  `CategoryTheory.Limits.pullback`, `pullback.fst`, `pullback.snd`; their signatures
  and docstrings were read. Scheme pullbacks are imported by PullbackCarrier.
- def-weil-residue-field: Mathlib.AlgebraicGeometry.ResidueField,
  `Scheme.residueField` and `Scheme.Hom.residueFieldMap`; signatures/docstrings read.
- lem-weil-pbc-fibre-product-points: Mathlib.AlgebraicGeometry.PullbackCarrier,
  `Scheme.Pullback.carrierEquiv`, `carrierEquiv_symm_fst`, `carrierEquiv_symm_snd`.
  Its recorded construction sends z to `⟨Triplet.ofPoint z, SpecOfPoint z⟩`;
  `SpecOfPoint z` is the preimage of the zero prime under ψ, hence its ideal is ker ψ.
  The theorem uses this same `Triplet.ofPoint`, `Triplet.tensor`, `tensorInl`,
  `tensorInr`, and `ofPointTensor` construction, all read in full.

Edge cases: empty schemes have no z and are covered vacuously. Nonmaximal tensor
primes are allowed: no quotient-field assumption is used in the first conjunct;
only the explicit final implication assumes it. No finite-type, algebraicity,
separability, characteristic, reducedness, or field-finiteness assumptions are
introduced. Universe u is arbitrary and matches Mathlib's Scheme category.
Ring equivalences between fields express field isomorphisms without extra data.

Searches made:
- msearch leansearch: "residue field of a point of a scheme pullback is isomorphic
  to the residue field of the tensor prime"; service unavailable (Internal Server
  Error), recorded as unavailable, with no verdict assigned.
- msearch leanfinder: "residue field of a point of the fibre product is the residue
  field of the prime in the tensor product of residue fields"; 8 hits, including
  ofPointTensor, Triplet.tensor, tensorInl, tensorInr, and general fibre lemmas;
  no theorem giving the required isomorphism.
- msearch loogle: "AlgebraicGeometry.Scheme.Pullback.ofPointTensor,
  PrimeSpectrum.ResidueField"; zero hits; the latter identifier is unknown
  (the actual ideal notion is Ideal.ResidueField).
- msearch grep: `ofPointTensor|ResidueField.*lift` in AlgebraicGeometry;
  8 hits, canonical-map and naturality constructions but no isomorphism theorem.
- rg in WeilConjectures, lean/Sheaf, and dag/lean_names_upstream.json for
  `ofPointTensor|lem-weil-pbc-fibre-product-point-residue-field`: no existing
  declaration, only a proof-docstring citation in FinitePiecePersistence. Read
  the entire Mathlib PullbackCarrier construction and the ideal residue-field
  API; no existing theorem states this claim.

Source checked: the local literature checkout has no schemes.tex, so opened
https://stacks.math.columbia.edu/tag/01JT, Lemma 26.17.5, statement and proof.
It states the residue-field correspondence and constructs the prime as the
kernel of ψ. No node fault, statement correction, or disputed statement found.
The declaration docstring carries all six proof steps of the node.

## Second reading by F1

I read the item's node and all four statement-dependency nodes, then the delivered
Lean file and the actual Mathlib declarations. Independent source reading: the
local Stacks checkout lacks schemes.tex; I read Tag 01JT at
https://stacks.math.columbia.edu/tag/01JT and the original schemes.tex at
https://raw.githubusercontent.com/stacks/stacks-project/master/schemes.tex,
from `lemma-points-fibre-product` through its proof. The section concerns arbitrary
schemes and morphisms: no standing finiteness, field-base, or separation assumption
needs an additional binder. The prime is explicitly the kernel in the source.

Object/hypothesis/conclusion checklist, in node order:

1. Arbitrary schemes X, Y, S: `{X Y S : Scheme.{u}}`; PASS. Scheme and Scheme.Hom
   in Mathlib/AlgebraicGeometry/Scheme.lean are respectively locally affine locally
   ringed spaces and morphisms of locally ringed spaces, as def-pc-scheme requires.
2. Morphisms f:X -> S and g:Y -> S: `(f : X ⟶ S) (g : Y ⟶ S)`; PASS. No property
   instance or field base is assumed.
3. Chosen fibre product and projections p,q: `pullback f g`, `pullback.fst f g`,
   `pullback.snd f g`; PASS. I opened HasPullback.lean:95--128 and the scheme
   HasPullbacks instance in Pullbacks.lean:485. These implement the recorded
   def-pc-fibre-product universal property with no extra hypothesis.
4. Point z: `(z : ↑(pullback f g))`; PASS. It is a scheme point, not a rational
   point or a closed point.
5. x=p(z), y=q(z), s=f(x)=g(y): `T := Triplet.ofPoint z`; PASS. I read Triplet,
   ofPoint, tensor, tensorInl and tensorInr in PullbackCarrier.lean. Its x and y
   are the projection images and its s is f(x), with hx=rfl and hy given by the
   pullback condition. No independent triple or equality is assumed.
6. Residue fields and their projection maps: `Scheme.residueField` and
   `Scheme.Hom.residueFieldMap`; PASS. In ResidueField.lean:45 and :123 these
   are the stalk quotient by its maximal ideal and the map of those quotients
   induced by the stalk map, exactly def-weil-residue-field.
7. Ring R = κ(x) tensor over κ(s) κ(y): `T.tensor`; PASS. It is the CommRingCat
   pushout of the two base-residue-field maps, with the required congruence
   identifications. This is the dependency's existing tensor model.
8. Canonical ring map ψ(a tensor b)=p-sharp(a)q-sharp(b):
   `ψ := (ofPointTensor z).hom`; PASS. Its definition is pushout.desc of the
   projection residue-field maps; hence its restrictions to both factors are
   exactly those maps. No arbitrary ring homomorphism is quantified.
9. Prime ideal attached to z: `p := RingHom.ker ψ` and
   `letI : p.IsPrime := RingHom.ker_isPrime ψ`; PASS. This instance is supplied,
   not assumed. I opened carrierEquiv and SpecOfPoint: its forward map uses
   the preimage of the zero prime under ψ, exactly this kernel. The two inverse
   projection lemmas agree with the dependency node's stated correspondence.
10. κ(p), the fraction field of R/p: `p.ResidueField`; PASS. I read Ideal.lean's
    definition and IsFractionRing instance: it is the residue field of the
    localization at p and canonically a fraction field of the quotient.
11. The induced field map κ(p) -> κ(z) is an isomorphism:
    `∃ e : p.ResidueField ≃+* (pullback f g).residueField z` with
    `e.toRingHom.comp (algebraMap T.tensor p.ResidueField) = ψ`; PASS.
    This equation fixes the induced map: Ideal.ResidueField.ringHom_ext at
    Ideal.lean:240 makes extensions unique. Thus this is equivalent to asserting
    the canonical map is an isomorphism, rather than just an abstract equivalence.
12. Compatibility with κ(x) and κ(y): the next two equalities compose that
    algebraMap with `T.tensorInl.hom` and `T.tensorInr.hom`, and compare with
    `((pullback.fst f g).residueFieldMap z).hom` and the snd analogue; PASS.
    Their direction and factor-field domains are correct.
13. In particular, if R/p is a field: `IsField (T.tensor ⧸ p) → ...`; PASS.
    This is only the antecedent of the second conjunct, not a hypothesis on
    the first isomorphism. No choice of Field instance is required.
14. Induced quotient map is an isomorphism of extensions of both factor fields:
    `∃ e : (T.tensor ⧸ p) ≃+* (pullback f g).residueField z`, followed by
    `e.toRingHom.comp (Ideal.Quotient.mk p) = ψ` and its two factor compatibility
    equalities; PASS. Surjectivity of Quotient.mk fixes the induced quotient
    map uniquely. The quantifier and implication order matches the node.

Edge cases: empty X or Y (and empty pullback) have no z, so the theorem is
vacuously applicable with no Nonempty assumption. A zero affine ring gives an
empty scheme, handled the same way; once z exists all residue fields are
nontrivial by the existing Field instances. Nonmaximal primes are included in
the first conjunct; only the second asks that the quotient be a field. For
example, the zero prime in Q(t) tensor over Q Q(s) need not be maximal, and
nothing here rules it out. No characteristic or separability restriction occurs.
There is no index set or n parameter. The universe u is bound and arbitrary,
as in Mathlib's Scheme and pullback category; no small-universe specialization
is imposed. Every term and implicit parameter is accounted for.

Independent searches, using different phrasing from the worker:

- msearch leanfinder, "The fraction field of the tensor quotient at a pullback
  point is canonically equivalent to its residue field": eight hits, including
  ofPointTensor, tensor, tensorInl/tensorInr and general residue-field-fiber
  correspondences; none states the required field isomorphism.
- msearch loogle, `AlgebraicGeometry.Scheme.Pullback.Triplet.SpecTensorTo`:
  twelve hits, including the two spectrum composite identities and projection
  identities. I read these in PullbackCarrier.lean; they provide construction
  and naturality, not the delivered residue-field isomorphism.
- msearch leansearch, "canonical field isomorphism at a prime associated to a
  fibre product point": service unavailable (Internal Server Error), recorded
  without a negative mathematical verdict.
- rg independently over Mathlib/AlgebraicGeometry, WeilConjectures, and
  lean/Sheaf for `residueField.*(equiv|iso)|IsIso.*residueField|ofPointTensor|
  SpecTensorTo`: hits for Spec.residueFieldIso, open-immersion residue maps,
  congruence maps, the PullbackCarrier construction and special fiber maps;
  no duplicate statement. Existing isomorphisms concern other objects or add
  hypotheses, and do not replace this declaration.

No new definition nodes or dependency modules are present or needed. No
statement_change is present; the original statement agrees with the source.
No mismatch was found, so the Lean and node record were retained. The only
change of this reading is this independent review section. The module has one
named theorem with sorry, no definition or additional proof; both docstrings
name Tag 01JT and the blueprint id. I compared all six node proof steps against
the declaration docstring: canonical map/kernel, tensor-spectrum morphism,
composition equal to the point, induced residue map and prime image, right
inverse, then bijectivity/compatibility and the field-quotient consequence all
appear in order. Namespace, header, import, and line lengths satisfy H9.

The node's lean.statement is byte-for-byte equal to the theorem signature
before `:= by`. Server scompile passed, exit code 0, compiled in 1.8 seconds,
with no errors or warnings. No unbound variable or universe remains.
