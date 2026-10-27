## Worker report

States `AlgebraicGeometry.exists_generic_orbit_dense_quotient` in
`Sheaf.AlgebraicGeometry.GenericOrbitDenseQuotient`. Its only proof is `by sorry`.
No definitions, new nodes, dependency repairs, or statement corrections are needed.
The node copy changes only `lean`; its statement, dependency lists, and accepted proof are unchanged.
All writes are in the assigned sandbox. No direct git commands or local Lean builds were run.

Source read: ILO Travaux de Gabber, X 2.3 Step 2, printed p.151 (PDF p.157),
which identifies the full quotient map as a universal homeomorphism on a dense open.
The node supplies the expanded subgroup-quotient and generic-algebra argument.
Also read the current blueprint's `def-sc-quasi-projective.md` in
`literature/blueprint/latest/`: it explicitly concerns arbitrary schemes over a field.
The module docstring carries all eight proof steps and their DAG dependencies.
Proof-only imports include every recorded project module used by those steps,
and the Mathlib modules named by the other proof dependencies' matches.

Hypotheses matched clause by clause:

- Field e: `(e : Type u) [Field e]`.
- The e-scheme structures are `b : B ⟶ Spec (.of e)` and `p : Y ⟶ Spec (.of e)`.
  The compatibility `hh : h ≫ b = p` makes h an e-morphism. Explicit structure maps
  match the existing quotient dependency's interface and the multiple maps over e.
- Nonempty finite disjoint union of integral finite-type schemes: `n : ℕ`,
  `Bᵢ : Fin (n + 1) → B.Opens`, `hcover : iSup Bᵢ = ⊤`, pairwise disjointness
  `hdisjoint`, and `hintegral : ∀ i, IsIntegral (Bᵢ i).toScheme`.
  Each integral open is nonempty. The finite disjoint open cover is clopen and presents
  exactly the integral components. A finite nonempty collection can always be indexed
  by `Fin (n+1)`, so this presentation excludes no such B.
  `[LocallyOfFiniteType b] [QuasiCompact b]` is finite type of B/e, equivalent to
  finite type of these finitely many clopen pieces: restriction preserves finite type,
  and a finite disjoint union of finite-type schemes is finite type.
- Reduced finite-type Y/e: `[IsReduced Y] [LocallyOfFiniteType p] [QuasiCompact p]`.
- Quasi-projective means the stated finite-dimensional projective-space immersion:
  `hp : IsQuasiProjective p` uses the existing upstream definition, whose finite
  coordinate type and `IsImmersion` give exactly that locally closed embedding.
- Finite group and action by e-automorphisms: `(G : Type v) [Group G] [Finite G]`,
  `a : G →* Aut Y`, and `ha : ∀ g, (a g).hom ≫ p = p`.
- Projective, surjective and invariant h: `hprojective : IsProjectiveBundle h`,
  `[Surjective h]`, and `hinvariant : ∀ g, (a g).hom ≫ h = h`.
  Projectivity uses the EGA/ILO finite-type quasi-coherent-module projective-bundle
  predicate, not an additional H-projectivity assumption over B.
- Every generic point maps to a generic with finite residue extension: `hgeneric`
  quantifies over every irreducible component C of Y and every generic ξ, concludes
  genericity of h ξ in some component D of B, and asserts
  `(h.residueFieldMap ξ).hom.Finite` for the actual induced field homomorphism.
- Each geometric generic fibre is one orbit: `horbit` quantifies over all components
  D of B and all generic η. Its t is constrained to be the canonical composite from
  the spectrum of `AlgebraicClosure (B.residueField η)` to B. This is a quantified
  alias of the canonical morphism, not an arbitrary geometric-point assumption.
  The fibre is nonempty and each pair x,y is carried to one another by a g in G.
  The two projection equations uniquely determine the induced base-change action
  morphism l, so an arbitrary fibre self-map cannot satisfy the hypothesis instead.

Conclusions matched clause by clause:

- Every subgroup, including the full and trivial subgroups: the simultaneous families
  `Q : Subgroup G → Scheme`, `q H : Y ⟶ Q H`, `d H : Q H ⟶ B`, and `∀ H`.
  Simultaneous choice is equivalent to the node's existence for each subgroup.
- Finite surjective admissible quotient: the existing
  `IsAdmissibleFiniteSchemeQuotient (a.comp H.subtype) (q H)` and `Surjective (q H)`.
  Unfolding that dependency gives orbit containment in affine opens, finiteness,
  invariance, quotient topology, point-orbit fibres, and injectivity with precisely
  invariant image on sections for every open. No private quotient definition is made.
- Factorization: `q H ≫ d H = h`.
- Reduced quotient: `IsReduced (Q H)` for every H.
- Orbit geometric fibres: for every algebraically closed field Ω and every
  `t : Spec Ω ⟶ Q H`, `pullback (q H) t` is nonempty and its points form one H-orbit.
  As in the recorded quotient theorem, both projection identities characterize the
  induced action. The element `g : H` acts by `a g`, using the subgroup inclusion.
- Categorical for invariant maps to arbitrary schemes: `∀ (Z : Scheme.{u}) (f : Y ⟶ Z)`,
  invariance under every `g : H` implies `∃! r : Q H ⟶ Z, q H ≫ r = f`.
  There are no reducedness, separation, finiteness, or base-linearity conditions on Z.
- Dense open containing every generic: `∃ U : B.Opens, Dense (U : Set B) ∧ ...`,
  with membership for every generic point of every irreducible component.
- The two finite maps: `IsFinite (h ∣_ U)` and
  `IsFinite (pullback.snd (d ⊤) U.ι)`. The latter is exactly Q_G ×_B U → U.
- Universal homeomorphism of the latter map:
  `(topologically IsHomeomorph).universally (pullback.snd (d ⊤) U.ι)`.
  This uses the exact recorded universal-base-change predicate, rather than only a
  homeomorphism before base change.
- Generic field spectrum: for every component generic η, an actual field L,
  `ι : B.residueField η →+* L` with `ι.Finite ∧ ι.IsPurelyInseparable`, and
  `j : (d ⊤).fiber η ≅ Spec (.of L)` satisfying the structure-map identity
  `j.hom ≫ Spec.map (CommRingCat.ofHom ι) = (d ⊤).fiberToSpecResidueField η`.
  Thus the isomorphism is over κ(η), which is the function field of that integral
  component; it does not merely identify the abstract underlying schemes.
- No normality, faithfulness, freeness, or group-order restriction appears anywhere.

Dependency declarations read and used:

| Node/notion | Module | Declaration |
| --- | --- | --- |
| def-kun-projective | WeilConjectures.AlgebraicGeometry.Morphisms.Projective | AlgebraicGeometry.IsHProjective; canonical finite-space convention underlying projectivity |
| def-pc-field-tower | Sheaf.FieldTheory.FieldTower | FieldExtension.degree and its docstring's Module.Finite/IsPurelyInseparable conventions; explicit map forms RingHom.Finite and RingHom.IsPurelyInseparable are used |
| def-pc-integral-scheme | Mathlib.AlgebraicGeometry.Properties | AlgebraicGeometry.IsIntegral |
| def-pc-reduced-scheme | Mathlib.AlgebraicGeometry.Properties | AlgebraicGeometry.IsReduced |
| def-per-admissible-finite-scheme-quotient | Sheaf.AlgebraicGeometry.AdmissibleFiniteSchemeQuotient | AlgebraicGeometry.IsAdmissibleFiniteSchemeQuotient |
| def-sc-generic-point | Mathlib.Topology.Sober | IsGenericPoint |
| def-trf-projective-bundle-morphism | Sheaf.AlgebraicGeometry.ProjectiveBundleMorphism | AlgebraicGeometry.IsProjectiveBundle |
| def-weil-field | Mathlib.Algebra.Field.Defs | Field |
| def-weil-finite-integral-morphism | Mathlib.AlgebraicGeometry.Morphisms.Finite | AlgebraicGeometry.IsFinite |
| def-weil-finite-type-morphism | Mathlib.AlgebraicGeometry.Morphisms.FiniteType; Morphisms.QuasiCompact | AlgebraicGeometry.LocallyOfFiniteType; AlgebraicGeometry.QuasiCompact |
| def-weil-geometric-fibre | Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback | CategoryTheory.Limits.pullback and its projections |
| def-weil-residue-field | Mathlib.AlgebraicGeometry.ResidueField | AlgebraicGeometry.Scheme.residueField; Scheme.Hom.residueFieldMap |
| def-weil-surjective-morphism | Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap | AlgebraicGeometry.Surjective |
| def-weil-universal-homeomorphism | Mathlib.CategoryTheory.MorphismProperty.Limits; Mathlib.AlgebraicGeometry.Morphisms.Constructors | CategoryTheory.MorphismProperty.universally; AlgebraicGeometry.topologically; IsHomeomorph |

Also uses the already recorded upstream `AlgebraicGeometry.IsQuasiProjective` in
`WeilConjectures.AlgebraicGeometry.ProjectiveSpace.QuasiProjective` (def-sc-quasi-projective).
Its full signature/docstring and actual immersion definition were read; nothing is restated.
The principal proof dependencies read were
`AlgebraicGeometry.exists_admissible_finite_type_field_quotient` (including its entire
geometric-fibre and relative-finiteness signature), `orbit_in_affine_of_quasiProjective`,
`orbit_in_affine_subgroup`, and
`Scheme.Hom.exists_dense_open_isFinite_of_finite_generic_fibers`.
The existing field-quotient theorem supplies precisely the geometric action equations
and arbitrary-target categorical clause used here. Its conclusion alone does not contain
this item's dense-open radiciality or generic purely inseparable field conclusion.

Edge cases checked before writing and again against the signature:

- Empty B is excluded exactly by the nonempty finite integral-component hypothesis;
  empty Y is then excluded by surjectivity. A one-component base has n=0.
- A zero-dimensional integral component is a field spectrum; its generic point is its
  only point, so U must contain it and the generic-field conclusion has its usual meaning.
- Disconnected B and a group permuting components of Y are allowed; generic hypotheses
  range over all components and there is a single dense open simultaneously on B.
- H=1, H=G, G=1, and a trivial or nonfaithful action are allowed. No transitivity of a
  subgroup's generic fibre is imposed; generic transitivity is only assumed for G.
- Singular or nonnormal reduced Y and nonnormal integral B are allowed.
- Characteristic zero forces the purely inseparable extension to be trivial;
  in positive characteristic nontrivial purely inseparable extensions and p dividing |G|
  are allowed. No characteristic or invertibility assumption was introduced.
- A geometric fibre can be nonreduced: only its points are required to be an orbit.
  Only the global quotient is asserted reduced. The field-spectrum clause concerns
  the ordinary generic fibre, not its potentially nonreduced geometric base change.
- All schemes/fields are in the common ambient universe u; the group has independent
  universe v. Algebraic closures and finite extensions exist in u, and all algebraically
  closed test fields of that ambient universe are quantified. No auto-bound variables.

Searches for an existing statement (all via the prescribed wrappers/read-only rg):

1. msearch leanfinder: "A finite group acting transitively on geometric generic fibres of
   a projective morphism gives a universal homeomorphism quotient over a dense open".
   Eight hits, including `PreGaloisCategory.exists_lift_of_quotient_openSubgroup`,
   `IsQuotientCoveringMap`, and covering-space results. None is this scheme statement.
2. msearch loogle: "AlgebraicGeometry.IsAdmissibleFiniteSchemeQuotient,
   AlgebraicGeometry.UniversallyInjective". Zero hits; the server index does not know
   the project's quotient predicate. Followed by the Mathlib-only query
   "AlgebraicGeometry.IsFinite, AlgebraicGeometry.Surjective": one hit,
   `Scheme.Hom.one_le_finrank_iff_surjective`, a finite-flat rank criterion, not this result.
3. msearch grep: `generic.*quotient|quotient.*generic|algebraicClosurePoint`
   in Mathlib/AlgebraicGeometry: zero hits.
4. msearch leansearch: "A finite group quotient is a universal homeomorphism over a dense
   open if the geometric generic fibres are single group orbits". Eight hits, on group
   quotients and topological quotient density; none addresses scheme generic fibres.
5. rg of `lem-sfb-generic-orbit-dense-quotient|generic.*quotient|quotient.*generic`
   in both lean/WeilConjectures and lean/Sheaf: no declaration for the item. Read the
   potentially relevant upstream AlgebraicGeometry/GenericQuotient.lean: its theorem
   concerns shrinking an affine finite-order automorphism quotient to a finite etale map,
   not this arbitrary finite-group projective morphism and dense universal homeomorphism.
   Read Sheaf/AlgebraicGeometry/FiniteQuotientGenericFields.lean: it assumes normality
   and gives generic stabilizer invariant fields, not the node's hypotheses or conclusion.
6. rg `exists_generic_orbit_dense_quotient` in lean/WeilConjectures, lean/Sheaf, and
   dag/lean_names_upstream.json: no existing declaration/name clash.

Validation: `scompile.py Q53 lem-sfb-generic-orbit-dense-quotient <module>` succeeded
for both the sandbox and actual library module (11.6s and 7.7s), with no errors or
unexpected warnings. The final docstring was reflowed without splitting DAG identifiers;
the subsequent dry run recompiles that final file. The Lean record's statement is copied
verbatim from the theorem keyword through the text immediately before `:=`.
No STATEMENT-DISPUTED issue or node fault was found.

## Second reading by Q53

This section records a second clause-by-clause self-check, not an independent agent review;
the dispatch brief prohibits starting agents and assigns independent review to the maintainer.
Reopened the node and complete module. Checked the conjunction boundaries: the geometric
fibre clause and arbitrary-target categorical clause are both inside `∀ H`, while the dense
open and generic-field clauses use `d ⊤`. Checked the residue-field orientation and the
isomorphism's equality over Spec κ(η); checked that both projection equations appear for
all induced fibre maps. Checked that the finite clopen cover allows a nonseparated base,
and that projectivity uses IsProjectiveBundle rather than imposing IsHProjective h.
No mathematical mismatch was found and no signature changed. Reflowed the proof docstring
to preserve complete DAG identifiers. The maintainer's independent review remains required.
