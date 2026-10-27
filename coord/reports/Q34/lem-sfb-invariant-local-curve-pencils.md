## Worker report

States `AlgebraicGeometry.exists_invariant_local_curve_pencils` in
`Sheaf.AlgebraicGeometry.InvariantLocalCurvePencils`, with one postponed theorem and two
fully constructed helper maps. The node is unchanged except for `lean`. No new nodes,
dependency repairs, or statement corrections are needed.

Source read: de Jong, Families of curves and alterations, §§3.3--3.5,
printed pp.605--606, publisher PDF https://www.numdam.org/item/10.5802/aif.1575.pdf.
Section 3.4 constructs invariant local finite maps with the requested generic avoidance;
section 3.5 takes a finite affine cover. Section 3.3 treats the field base separately.
The node supplies the detailed sixteen-step norm-section proof, including its separable
constant extension in that case; all sixteen steps and their dependency citations are in
the theorem docstring. The proof remains `sorry`.

Hypotheses, individually:

- Field k: `(k : Type u) [Field k]`.
- Schemes over k: `S X : Scheme.{u}`, `pS`, `pX`; `hf : f ≫ pS = pX` fixes
  the k-structure on the relative curve, rather than allowing unrelated structure maps.
- Integral S and X: `[IsIntegral S] [IsIntegral X]`.
- Normal S: `hnormal` asserts an integrally closed domain at every stalk.
- Projective S/k: `[IsHProjective pS]`, using the node's finite embedding convention.
- Finite type S/k and X/k: `[LocallyOfFiniteType pS] [QuasiCompact pS]` and the
  corresponding two instances for `pX`.
- Relative H-projectivity: `(f : X ⟶ S) [IsHProjective f]`.
- Pure geometric curve fibres: `hpure` tests `pullback f s` for every algebraically
  closed field and every geometric point, using `.IsPureDimension 1`.
- K is the actual function field `S.functionField`, not an arbitrary field.
  C is the actual generic fibre `pullback f S.fromSpecFunctionField`.
- Smooth and geometrically integral C: the two class hypotheses on `pullback.snd`.
- Reduced finite etale generic marking: `M : Closeds C`, represented by its reduced
  closed subscheme `(Scheme.IdealSheafData.vanishingIdeal M).subschemeι`.
  `hMfinite` and `hMetale` concern its composite to `Spec K`. This presentation
  covers every reduced closed subscheme because its ideal is radical. Reducedness
  also follows from etaleness over the field.
- Finite group and action: `J : Type v`, `[Group J] [Finite J]`, `σ : J →* Aut X`.
  `hJ` says the action is over S; faithfulness and invertibility of its order are
  not assumed. It therefore fixes K. No k-linear action is imposed separately.
- Preservation of M: `hMstable` tests generic points x,y whose images in X are
  related by σ, and requires `x ∈ M ↔ y ∈ M`. The generic-fibre projection is a
  monomorphism, and the action over S canonically transports each x to such a y,
  so this is exactly stability of the reduced marking, without an extra chosen action.

Conclusion, clause by clause:

- `hη` and the existential `Algebra S.functionField X.functionField` expose the
  induced function-field inclusion. Its `algebraMap` is REQUIRED to equal the
  generic stalk map written immediately afterward; this is no arbitrary algebra.
  Dominance is a conclusion, as it follows from the nonempty generic curve.
- Existential `E : Type u`, `Field E`, `Algebra K E`, `Module.Finite K E`,
  `Algebra.IsSeparable K E` is the finite separable extension.
- `IsDomain (X.functionField ⊗[K] E)` records that the tensor product has a
  fraction field. The literal compositum in the statement is
  `FractionRing (X.functionField ⊗[K] E)`, with its canonical left algebra.
  Geometric integrality is precisely what makes this a domain; no arbitrary
  compositum field or abstract identification replaces it.
- `S.normalizationIn E` and `X.normalizationIn (FractionRing ...)` are the
  node's exact normalizations from its recorded dependency.
- `q` is their structural map. Its composite to S is the given map from X, and
  its composite with `Spec` of the compositum is REQUIRED to be the right tensor
  inclusion followed by the canonical `Spec E` map into the base normalization.
  These equalities fix q canonically, by density of the generic point and
  separatedness of the finite base normalization. They do not assert existence
  of an unconstrained map between models.
- `τ : J →* Aut X_E`, with the two equivariance equations, extends σ and acts
  over the identity of S_E. The generic equation for q then forces this extension
  to fix the embedded E pointwise. Thus its field action is the prescribed one.
- `r : ℕ`, `U : Fin r → S_E.Opens`, `iSup U = ⊤`, `IsAffineOpen (U i)`
  give the finite affine open covering.
- `φ : pullback q (U i).ι ⟶ ProjectiveLine (U i).toScheme`, with its structural
  equality, `IsFinite φ`, and `Surjective φ`, is the required finite surjective
  U_i-morphism. `τi` is fixed by its composite with the open immersion into X_E;
  the equation `(τi j).hom ≫ φ = φ` is scheme-theoretic invariance, not just
  invariance on underlying points.
- `e` factors the canonical generic E-point through U_i. It exists for every
  nonempty open of the integral base. Empty redundant opens can be discarded.
- `ψ` is the generic pencil: its structural projection and its composite with
  `ProjectiveSpace.map ... e` equal the base-changed structural map and φ.
  These two equalities characterize ψ uniquely by the projective-space pullback.
  The iterated source is precisely `(X_E)_{U_i} ×_{U_i} Spec E`, canonically C_E:
  normalization of the smooth geometrically integral scalar-extended generic
  curve is that curve itself. The use of an iterated pullback keeps every
  comparison typed without any chosen equality between pullback objects.
- `c` has both its composites to X and Spec K prescribed. It is the canonical
  map from that generic curve to C and fixes the meaning of M_E.
- `∃ V, Nonempty V ∧ Etale (V.ι ≫ ψ)` is generic etaleness. On an integral curve
  any nonempty open is dense, so no entire-curve etaleness is imposed.
- `invariantPencilSpecialPoint` constructs `[0:1]`, `[1:1]`, `[1:0]` in order.
  For EACH `j : Fin 3`, `IsFinite (pullback.snd ψ point)` and `Etale ...`
  state that the actual scheme-theoretic fibre is finite etale over E.
  Such a scheme is reduced; the three distinct fibres are disjoint, hence their
  union is reduced finite etale too. Conversely the finite-etale union restricts
  to these three open-and-closed pieces. For these finite maps of smooth curves,
  this is also the node's equivalent etaleness at every point over the three values.
- The final universal clause states that a point of ANY of the three fibres has
  `c z ∉ M`. This is the additional disjointness from M_E, separately from etaleness.
- `0 < topologicalKrullDim S → Function.Bijective (algebraMap K E)` says E=K
  as an extension in positive base dimension. Bijectivity gives the unique
  K-algebra identification, rather than just an abstract field isomorphism.
- If `topologicalKrullDim S = 0`, `r = 1` and `IsIso` of the canonical map
  `Spec E ⟶ S_E` say one open suffices and S_E=Spec E. `IsIso` of the generic
  pullback projection to X_E says X_E=C_E. These are canonical identifications,
  avoiding artificial literal equality of scheme encodings.

Dependency declarations read and used:

- `Field`, Mathlib.Algebra.Field.Defs, through the foundational imports.
- `AlgebraicGeometry.IsIntegral`, Mathlib.AlgebraicGeometry.Properties.
- `AlgebraicGeometry.LocallyOfFiniteType`, Mathlib.AlgebraicGeometry.Morphisms.FiniteType,
  and `QuasiCompact`, Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact.
- `AlgebraicGeometry.IsFinite`, Mathlib.AlgebraicGeometry.Morphisms.Finite.
  The same node also records integral morphisms, not needed in this signature.
- `AlgebraicGeometry.Smooth`, Mathlib.AlgebraicGeometry.Morphisms.Smooth.
- `AlgebraicGeometry.GeometricallyIntegral`, Mathlib.AlgebraicGeometry.Geometrically.Integral.
- `AlgebraicGeometry.IsHProjective`, WeilConjectures.AlgebraicGeometry.Morphisms.Projective.
- `Scheme.functionField` and `Scheme.fromSpecFunctionField`, from
  Mathlib.AlgebraicGeometry.FunctionField, imported through the recorded
  WeilConjectures.AlgebraicGeometry.FunctionField. The dependency's component
  product definition is unnecessary for these integral schemes; its node explicitly
  supplies the arbitrary integral-scheme clause by Mathlib.functionField.
- `Algebra`, Mathlib.Algebra.Algebra.Defs.
- `Scheme.normalizationIn`, `Scheme.fromNormalizationIn`, and
  `Scheme.fromSpecOfAlgebraFunctionField`,
  WeilConjectures.Mathlib.AlgebraicGeometry.Normalization.
- `AlgebraicGeometry.Etale`, Mathlib.AlgebraicGeometry.Morphisms.Etale.
- `Scheme.IsPureDimension`, Sheaf.AlgebraicGeometry.PureDimension.
- `ProjectiveSpace` and its `map`, WeilConjectures.AlgebraicGeometry.ProjectiveSpace;
  `ProjectiveLine` is the existing abbreviation for two homogeneous coordinates.
  The existing affine chart, `AffineSpace.homOfVector`, and `ProjectiveLine.infinity`
  construct the standard three sections in the imported ProjectiveSpace.Line module.

All recorded proof-dependency modules are imported non-publicly, except modules
already public for the signature. The four as-yet unstated proof prerequisites
(finite-normal-relative-curve-model, ample-curve-two-section-pencil,
ample-fibre-section-lifting, separating-pair-open) have no module to import.
No import of the downstream HighGenusEquivariantCover is added, to avoid a future cycle.

Edge cases checked before writing: empty M is admitted; J may be trivial or have
nontrivial kernel; the group order may be divisible by the characteristic; finite k
and dimension-zero bases are admitted and may require a nontrivial E; positive base
dimension forces the chosen extension to be trivial; the three rational values remain
distinct in characteristic two; the integral base is nonempty and so an empty covering
cannot satisfy the cover equation; empty geometric fibres satisfy pure dimension
vacuously as in the dependency, while the integral smooth generic fibre is nonempty.
There is no extraneous algebraic-closure hypothesis on k, K, or E. All universes and
variables are explicit and `autoImplicit` is disabled. No `let`, private definition,
local instance, axiom, or unprescribed choice of comparison map is used.

Searches made:

- msearch.py leanfinder: `A projective family of curves admits finite group invariant
  separating pencils locally on the base avoiding zero one infinity` and
  `Finite invariant morphisms from curves to the projective line`. The eight hits
  concerned Weierstrass curves, unrelated polynomial results, or finite global
  sections. None states the local invariant pencil assertion.
- msearch.py loogle: `AlgebraicGeometry.IsFinite, AlgebraicGeometry.ProjectiveSpace`.
  Zero hits (the service does not know the project's ProjectiveSpace).
- msearch.py grep: `invariant.*pencil|pencil.*invariant`: zero Mathlib hits.
- rg over lean/WeilConjectures and lean/Sheaf for
  `invariant.*[Pp]encil|[Pp]encil.*invariant|lem-sfb-invariant-local-curve-pencils`:
  only the downstream high-genus-cover proof cites this lemma; no theorem exists.
  Related equivariant curve-pencil material concerns a different birational
  preparation and does not supply this local finite-pencil theorem.
- rg for the proposed declaration names in those two libraries and
  dag/lean_names_upstream.json: no collisions.
- Read existing projective-line coordinate constructions, generic stalk maps,
  normalization-in-extension, and Mathlib tensor inclusion/fraction-ring APIs;
  reused these constructions instead of defining alternate notions.

Validation: scompile.py compiled the delivered file both under its sandbox name and
its final library name against the live server build, within 60 seconds, with no
errors or unexpected warnings. No statement is disputed.

## Second reading by Q34

The dispatcher explicitly forbids starting another agent, so this section records
an author's second pass, not a fabricated independent review. The maintainer's
independent delivery review remains required. Reopened the node and the complete
signature and checked each hypothesis and conclusion against the mapping above.
In particular checked that the marking is on C itself, that the function-field algebra
and constant embedding are canonical, that invariance is an equality of morphisms,
that both generic comparison projections are fixed, and that the zero-dimensional
clause and separate disjointness condition are present. No mismatch was found.
