## Worker report

The module `Sheaf.AlgebraicGeometry.AbelianNeronModel` states
`AlgebraicGeometry.exists_abelian_neron_model`, with its entire proof `sorry`.
The item statement, dependencies and proof plan are unchanged. There are no new
nodes, helper definitions or dependency repairs. No statement dispute was found.

Clause-by-clause correspondence:

- D is a Noetherian integrally closed domain: `(D : Type u) [CommRing D]
  [IsDedekindDomain D]`. Mathlib's class includes dimension at most one, so
  `(hD : ringKrullDim D = 1)` retains the item's explicit dimension exactly one.
- E is its fraction field: `(E : Type u) [Field E] [Algebra D E]
  [IsFractionRing D E]`. This permits any chosen realization of the fraction
  field and uses its given embedding, without replacing the generic map by an
  arbitrary map. S is exactly `Spec (.of D)` throughout.
- A/E is the given abelian variety and group structure: `(A : Over (Spec (.of E)))
  [GrpObj A] [IsAbelianVariety A]`. The recorded predicate asserts properness,
  smoothness and connectedness; the separately supplied `GrpObj` supplies the
  group operations, as its source docstring explicitly requires.
- The model and its group diagrams: `∃ G : Grp (Over (Spec (.of D)))`. Its
  underlying scheme over S is `G.X`, with structural morphism `G.X.hom`.
  Mathlib's `GrpObj` packages multiplication, unit, inverse and their diagrams;
  `IsCommMonObj G.X` supplies the commutativity diagram.
- Smooth and separated: `Smooth G.X.hom ∧ IsSeparated G.X.hom`.
  The latter class is defined by `IsClosedImmersion (pullback.diagonal G.X.hom)`.
- Finite type (and hence locally finite type): `LocallyOfFiniteType G.X.hom ∧
  QuasiCompact G.X.hom`. These are precisely the two clauses in the recorded
  finite-type dependency. No properness or connected-fibre requirement is added
  to the integral model.
- The generic E-group isomorphism is the existential `e` in `Grp (Over (Spec E))`:
  its source is `(Over.pullback (Spec.map (CommRingCat.ofHom
  (algebraMap D E)))).mapGrp.obj G`, its target `Grp.mk A`. Thus the isomorphism
  respects the supplied group structure on A and the canonical base-changed
  group structure on G, as opposed to being only a scheme isomorphism.
- For every smooth S-scheme: `∀ (X : Over (Spec (.of D))), Smooth X.hom → ...`.
  No quasi-compactness, finite type, nonemptiness, separation or group structure
  is imposed on X.
- Restriction is a bijection: `Function.Bijective (fun f : X ⟶ G.X ↦
  (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap D E)))).map f ≫
  (Grp.forget (Over (Spec (.of E)))).map e.hom)`.
  Its domain is Hom_S(X,G), its target Hom_E(X_E,A); the function is precisely
  canonical base change followed by the chosen generic identification. Both
  injectivity (uniqueness) and surjectivity (existence) are asserted.
- No excellence, completeness or residue-field perfection appears in any binder.
  There is no choice or missing data in a definition: the only new declaration
  is the theorem with its postponed proof.

Recorded statement dependencies read and used:

- `def-pc-scheme`: `Mathlib.AlgebraicGeometry.Scheme`, declarations
  `AlgebraicGeometry.Scheme` and `AlgebraicGeometry.Scheme.Hom`.
- `def-weil-affine-spectrum`: the same module, `AlgebraicGeometry.Spec` and
  `AlgebraicGeometry.Spec.map`, with the fraction-field algebra map.
- `def-pc-base-change`:
  `WeilConjectures.AlgebraicGeometry.BaseChangeConventions`, whose module
  docstring prescribes `CategoryTheory.Over.pullback` for scheme/morphism base
  change; its recorded `Scheme.Modules.moduleBaseChange` is specifically for
  modules and is not misused as scheme base change.
- `def-sbc-smooth-morphisms`: `Mathlib.AlgebraicGeometry.Morphisms.Smooth`,
  `AlgebraicGeometry.Smooth` (the current name, not deprecated `IsSmooth`).
- `def-weil-closed-immersion`:
  `Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion`,
  `AlgebraicGeometry.IsClosedImmersion`, via the exact diagonal definition of
  `IsSeparated` in `Mathlib.AlgebraicGeometry.Morphisms.Separated`.
- `def-weil-finite-type-morphism`:
  `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`,
  `AlgebraicGeometry.LocallyOfFiniteType` and `AlgebraicGeometry.QuasiCompact`.
- `def-sc-abelian-variety`:
  `WeilConjectures.AlgebraicGeometry.AbelianVariety.Defs`,
  `AlgebraicGeometry.IsAbelianVariety`, full signature and docstring read.

Additional existing primitives are Mathlib's `IsDedekindDomain`, `ringKrullDim`,
`IsFractionRing`, `CategoryTheory.Grp`, `GrpObj`, `IsCommMonObj`, `Functor.mapGrp`
and `Grp.forget`. Their definitions were inspected. In particular `mapGrp` uses
`Over.pullback`'s finite-product-preserving monoidal structure, not a freely
chosen generic-fibre group law.

The module imports the already stated proof dependencies: Dedekind localization
(Mathlib.RingTheory.DedekindDomain.Dvr), strict henselization (the upstream
StrictHenselization module), strict-henselization DVR (Sheaf's
StrictHenselizationDVR), abelian projectivity (upstream AbelianVariety.Projective),
properness (available through AbelianVariety.Defs), finiteness of closed points
(Sheaf's FiniteOfIsClosedOfClosedPoints), smooth base change/composition
(Mathlib.RingTheory.Smooth.Basic), and commutativity (upstream
AbelianVariety.Basic). Four proof nodes currently have no Lean record:
lem-sfb-bounded-group-local-neron-criterion,
lem-sfb-abelian-dense-open-spreading,
lem-sfb-abelian-scheme-neron-property,
lem-sfb-neron-finite-complement-patching. They are recorded in the theorem's
four-step proof docstring and require no import until stated. None is needed
to type this statement.

Edge cases checked: dimension-zero fields are excluded because the node
explicitly defines Dedekind domains to have dimension one; zero-dimensional
abelian varieties are included (no positive-dimension hypothesis on A);
empty and arbitrary non-quasi-compact smooth test schemes are included; the
model is not required to have connected fibres or to be proper; all residue
characteristics and imperfect residue fields are allowed. All schemes and the
base and fraction fields use the same arbitrary universe u, matching the
project's scheme and base-change APIs, with no independent smaller universe
for test schemes. All variables and universes are explicitly bound and
`autoImplicit` is disabled.

Searches performed before writing:

- `msearch.py ... leanfinder "An abelian variety over the fraction field of a
  Dedekind domain has a finite type smooth separated Neron model with the
  mapping property for all smooth schemes"`: eight results about Weierstrass
  minimal/integral models and good reduction, none a Néron mapping theorem.
- `msearch.py ... loogle '"Neron"'`: OK, zero hits.
- `msearch.py ... grep 'Neron|Néron|neron'`: OK, zero Mathlib hits.
- `rg -n -i 'neron|néron' lean/Sheaf lean/WeilConjectures`: no existing
  Néron definition or theorem. The broader group/abelian search found the
  existing `Grp`, base-change and abelian-variety interfaces reused here.
- `rg -n 'lem-sfb-abelian-neron-model' lean/WeilConjectures
  dag/lean_names_upstream.json`: no existing declaration for this item.
- DAG concept search found the accepted local existence, open spreading,
  patching and semiabelian lemmas, none an existing recorded copy of this
  theorem. No missing independent notion is introduced: the inline definition
  of Néron mapping property in the item is rendered directly with existing
  Hom types, canonical functors and Function.Bijective.

The primary-source scan named by the node was opened at
https://www.math.stonybrook.edu/~kamenova/homepage_files/Bosch_Raynaud_Neron_Model_tc.pdf.
BLR 1.2 Definition 1 and Proposition 6, 1.3 Corollary 2 and 1.4 Theorem 3 agree
with the model properties, generic group identification and unrestricted
smooth-test mapping property used here. No source correction was necessary.

Validation: prescribed server `scompile.py` compiled the single module cleanly
against the published live build (sandbox 3.5 s; library module 4.0 s), with
no errors or non-sorry warnings. The dry-run and delivery results are recorded
below after the required preflight.

## Second reading by Q73

The dispatcher explicitly requires a single worker with no subagents and an
independent maintainer review after delivery. This is a self-audit, not a claim
of an independent worker reading. I reread the node, dependency definitions and
the complete signature together. The dimension-one convention is retained by
hD; the supplied group law on A is retained by Grp.mk A; e is a group
isomorphism, and its underlying map is the very map used in restriction. In
particular the smooth test scheme X is not required to be a group. The finite
type condition is the locally-finite-type/quasi-compact conjunction, and the
full mapping property includes both existence and uniqueness. No mismatch
requiring a statement change was found. The maintainer's independent review
remains the independent mathematical check.

Dry run: `deliver2.py Q73 lem-sfb-abelian-neron-model --no-push` printed
`OK (dry run): commit a7243baf86d passes the preflight and compiles; nothing pushed`.
