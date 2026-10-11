## Worker report

Module: `Sheaf.AlgebraicGeometry.SteinFactorizationAffine`; declaration:
`AlgebraicGeometry.Scheme.Hom.steinFactorization_affine`. This is one theorem with
`by sorry`, no definitions, no auxiliary proofs, and no change to the natural-language
statement or dependency list.

Hypothesis and clause correspondence:

- Commutative ring A: `{A : Type u} [CommRing A]`, with no Noetherian, domain, or
  nontriviality assumption.
- Scheme X and morphism to Spec A: `{X : Scheme.{u}}` and
  `(f : X ⟶ Spec (CommRingCat.of A))`.
- Properness of f: `[IsProper f]`, precisely the recorded proper-morphism definition.
- B is H^0(X,O_X): `Γ(X, ⊤)`, the structure sheaf's ring of global sections, rather
  than a separately chosen ring with additional identifications.
- The Stein factorization: q is the canonical `X.toSpecΓ`; s is the recorded
  `f.steinFactorizationBase`, whose definition is
  `Spec.map ((Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫ f.appTop)`. The dependency's
  `Scheme.toSpecΓ_steinFactorizationBase f` states that q followed by s equals f.
  The statement uses these canonical maps directly; it does not quantify over
  arbitrary factorizations or require extra hypotheses.
- (i) A → B integral: `((Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫ f.appTop).hom.IsIntegral`.
  This is exactly the ring map defining s; the isomorphism transports the source
  from Γ(Spec A,O) to A. RingHom.IsIntegral means every element is integral under
  this map, equivalently annihilated by a monic polynomial with coefficients from A.
- (ii) q proper: `IsProper X.toSpecΓ`.
- (iii) geometrically connected fibres: `GeometricallyConnected X.toSpecΓ`.
  Mathlib's definition quantifies over all field-valued base changes and uses
  ConnectedSpace, which includes nonemptiness; its fibre characterization is
  `GeometricallyConnected.iff_geometricallyConnected_fiber`.
- For every t in Spec B: `∀ t : Spec Γ(X, ⊤)`.
- The scheme-theoretic fibre is connected, in particular nonempty:
  `ConnectedSpace (X.toSpecΓ.fiber t)`. `ConnectedSpace.toNonempty` supplies
  nonemptiness; it is not merely preconnectedness.
- The subspace q⁻¹(t) is connected and nonempty:
  `_root_.IsConnected (X.toSpecΓ ⁻¹' {t})`, the set form of connectedness.
- The fibre maps homeomorphically onto that subspace: the recorded fibre
  definition supplies `(X.toSpecΓ).fiberHomeo t`, and its `fiberHomeo_apply`
  identifies its underlying map with `(X.toSpecΓ).fiberι t`. This clause is part
  of the dependency's established fibre construction, explicitly named in the
  theorem docstring, rather than a second copy or a tautological conjunct.

Dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Morphisms.Proper`: `AlgebraicGeometry.IsProper`
  (extends IsSeparated, UniversallyClosed, LocallyOfFiniteType; universal
  closedness also supplies quasi-compactness, so this agrees with finite type).
- `WeilConjectures.Mathlib.AlgebraicGeometry.GammaSpecAdjunction`:
  `AlgebraicGeometry.Scheme.Hom.steinFactorizationBase` and
  `AlgebraicGeometry.Scheme.toSpecΓ_steinFactorizationBase`.
- `Mathlib.AlgebraicGeometry.Fiber`: `AlgebraicGeometry.Scheme.Hom.fiber`,
  `fiberι`, `fiberToSpecResidueField`, `fiberHomeo`, `fiberHomeo_apply` (available
  through the geometric-connectedness import).
- `Mathlib.Topology.Connected.Basic`: `ConnectedSpace`, the connected-scheme
  node's Mathlib match, including its nonemptiness field.
- `Mathlib.AlgebraicGeometry.Geometrically.Connected`:
  `AlgebraicGeometry.GeometricallyConnected`; no private replacement.

Edge cases checked before writing: A may be the zero ring, X may be empty,
A need not be Noetherian or a domain, and disconnected X is allowed. For empty
X, B is the zero ring and Spec B is empty, so the pointwise conclusions are
vacuous; geometric connectedness of the empty map to the empty intermediate
scheme is consistent. For nonempty intermediate spectrum, ConnectedSpace
excludes empty fibres. Universes are explicit (`u`, `A : Type u`, `Scheme.{u}`),
with no independent smaller universe of field tests or hidden automatic binders.

Searches made on 2026-10-11:

- `msearch.py ... leanfinder`: "Stein factorization of a proper morphism to Spec A
  has integral global sections and proper canonical map with geometrically
  connected fibres". Eight hits, including `isIntegral_appTop_of_universallyClosed`,
  integral normalization maps, `IsIntegralHom`, and
  `IsIntegralHom.iff_universallyClosed_and_isAffineHom`. These give only a clause
  or a different factorization, not the requested theorem.
- `msearch.py ... loogle`: "AlgebraicGeometry.GeometricallyConnected,
  AlgebraicGeometry.IsProper". OK, zero hits.
- `msearch.py ... leansearch`: "proper scheme Stein factorization geometrically
  connected canonical morphism to spectrum of global sections". UNAVAILABLE:
  service unavailable, Internal Server Error. No verdict drawn from this service.
- `msearch.py ... grep` in AlgebraicGeometry:
  `stein|toSpecΓ.*[Cc]onnect|[Pp]roper.*toSpecΓ`. One irrelevant quasi-separatedness
  hit; no Stein theorem.
- `rg` with the same expression in WeilConjectures and lean/Sheaf: canonical
  Stein factorization definition and HenselianConnectedness results. The latter's
  `isFinite_steinFactorizationBase` assumes Noetherian A and concerns s, while
  its connectedness results concern henselian closed fibres, not this statement.
- `rg` for the exact node id in WeilConjectures: no hits.
- `rg` for `steinFactorization_affine` in WeilConjectures, Mathlib, lean/Sheaf,
  and dag/lean_names_upstream.json: no hits; declaration name is fresh.

Source checked directly: https://stacks.math.columbia.edu/tag/03H2 (the local
literature/stacks-project/more-morphisms.tex is not installed on this machine).
Its clauses (1), (2), and (4) give precisely the affine assertion, with no
Noetherian restriction. There is no statement dispute or correction.
The imported proof's formal-functions description differs from the current
source proof, which uses Tag 0G7X and principal localization to lift a fibre
idempotent, then factors through the residue field. The theorem docstring
records all six DAG proof steps and notes this source difference for stage 3;
it does not silently alter the DAG proof. No proof is attempted in stage 2.

Validation: server compilation initially found the ambiguous unqualified
`IsConnected` (CategoryTheory vs topology); changed it to `_root_.IsConnected`.
The final server compile and delivery dry run are performed with the prescribed
tools. The second reading is reserved for the independent reader.


## Second reading by Q1

I independently opened the item node, its Lean module, all four statement-dependency
nodes and their recorded Lean declarations. I read the Stacks TeX source fetched from
https://raw.githubusercontent.com/stacks/stacks-project/master/more-morphisms.tex,
section `section-stein-factorization` and theorem `theorem-stein-factorization-general`,
lines 15079–15086 and 15289–15357 (also checked Tag 03H2 online). The section imposes
no standing Noetherian, field, nonempty, or finite-presentation hypothesis.

Object, hypothesis and conclusion checklist, in the node's order:

1. A commutative ring A: `{A : Type u} [CommRing A]`. PASS: no domain,
   nontriviality, Noetherianity or characteristic restriction.
2. X a scheme and f a morphism to Spec A: `{X : Scheme.{u}}` and
   `(f : X ⟶ Spec (CommRingCat.of A))`. PASS: these are exactly the objects named.
3. f proper: `[IsProper f]`. PASS: opened Proper.lean:42; the class requires
   separatedness, universal closedness and local finite type. Universal closedness
   supplies quasi-compactness, so this is the node's finite-type definition.
4. B = H^0(X,O_X): `Γ(X, ⊤)`. PASS: actual structure-sheaf global sections,
   with no arbitrary B or extra identification hypothesis.
5. q and s the Stein maps: `X.toSpecΓ` and the ring map
   `((Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫ f.appTop).hom`. PASS: opened
   GammaSpecAdjunction.lean:42–60. `f.steinFactorizationBase` is exactly Spec.map
   of this map; `Scheme.toSpecΓ_steinFactorizationBase f` proves the composite
   is f. No additional factorization equality is needed as a hypothesis/conclusion.
6. Clause (i), integral A → B: the above `.hom.IsIntegral`. PASS: every element
   of B is integral under the induced map from A, not module-finite over A.
7. Clause (ii), q proper: `IsProper X.toSpecΓ`. PASS.
8. Clause (iii), geometrically connected fibres: `GeometricallyConnected
   X.toSpecΓ`. PASS: opened Connected.lean:40 and Basic.lean:46; it requires
   ConnectedSpace after every field-valued base change. Its fibre equivalence
   is `GeometricallyConnected.iff_geometricallyConnected_fiber`.
9. For each t in Spec B: `∀ t : Spec Γ(X, ⊤)`. PASS: the quantifier follows
   the three global clauses and requires no chosen point or nonemptiness.
10. Scheme-theoretic fibre X_t connected and nonempty:
    `ConnectedSpace (X.toSpecΓ.fiber t)`. PASS: Fiber.lean:38 uses the pullback
    along the canonical residue-field morphism. ConnectedSpace at Basic.lean:705
    extends PreconnectedSpace and contains `toNonempty`.
11. Inverse-image subspace connected and nonempty:
    `_root_.IsConnected (X.toSpecΓ ⁻¹' {t})`. PASS: set connectedness includes
    nonemptiness, and the root qualifier avoids CategoryTheory.IsConnected.
12. X_t maps homeomorphically onto that subspace: PASS through the dependency
    `def-pc-scheme-fibre`, not a missing new claim. Opened Fiber.lean:94–108:
    `X.toSpecΓ.fiberHomeo t` is the homeomorphism and `fiberHomeo_apply` identifies
    its map with `fiberι t`. The module docstring explicitly cites these.

Edge cases: the zero ring is allowed; Spec A is then empty and a morphism from X
forces X empty. Empty X over any A is allowed, with zero global-section ring and
empty Spec B, hence no t and no field-valued point of Spec B. The pointwise and
geometric clauses are consequently vacuous, without falsely declaring an empty
space connected. Disconnected X, arbitrary characteristic and non-Noetherian A
are allowed. There is no index set or n in this statement. The shared explicit
universe u for A, schemes and Mathlib's test fields introduces no independent
smaller universe that could make geometric connectedness vacuous; schemes/rings
of different original sizes can be represented in a common universe. All variables
are bound, and there is no hidden auto-implicit binder.

Independent searches used different wording from the worker:

- LeanFinder: "The canonical affinization of a proper scheme over a ring is proper
  and has geometrically connected fibers". Eight hits about finite/affine proper
  morphisms, Proj and valuative criteria; none states this theorem.
- Loogle: `AlgebraicGeometry.Scheme.toSpecΓ,
  AlgebraicGeometry.GeometricallyConnected`. Zero hits.
- LeanSearch: "The affinization morphism from a proper scheme to the spectrum of
  its global functions has geometrically connected fibers". Service unavailable
  (Internal Server Error); no mathematical verdict inferred.
- msearch grep: `affinization|geometricallyConnected.*toSpec|toSpecΓ|steinFactor`
  in AlgebraicGeometry; hits concern the canonical map and affine schemes, not
  properness and geometric connectedness of this factorization.
- Direct rg in WeilConjectures and project lean/Sheaf:
  `affinization|steinFactor|toSpecΓ.*(proper|connected)|(proper|connected).*toSpecΓ`.
  Opened HenselianConnectedness.lean:52–75: its Stein-base finiteness theorem
  requires Noetherian A and gives a property of s, not q. Its connectedness theorem
  concerns henselian closed fibres, not the current general statement. The existing
  canonical factorization definition is used, not duplicated.
- Checked the exact declaration name and blueprint id in WeilConjectures and
  dag/lean_names_upstream.json; no existing copy of this statement found.

No new definition nodes, dependency modules or statement correction are present
or needed. All four dependency notions are usable as recorded. No mismatches found;
I preserved the Lean module and node verbatim. The source proof differs from the
DAG's formal-functions route, which may need stage-3 repair; the docstring already
records that difference and faithfully carries all six DAG proof steps and their
named dependencies. This does not change the source's theorem statement.

H5/H6/H8/H9 checks: no definitions or hollow data, one named theorem with `sorry`,
no proof attempted, source and blueprint in both docstrings, six proof steps,
standard namespace/header, no private definitions/local notation/instances, and
all lines at most 100 characters. The node's `lean.statement` was checked verbatim
against the complete file signature. Server scompile succeeded in 1.8 seconds with
no warnings. Delivery dry run and final delivery follow this reading.
