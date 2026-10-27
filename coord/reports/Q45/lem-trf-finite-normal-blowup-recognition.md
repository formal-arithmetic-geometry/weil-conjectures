## Worker report

The single module `Sheaf.AlgebraicGeometry.FiniteNormalBlowupRecognition` states
`AlgebraicGeometry.Scheme.IdealSheafData.finite_normal_blowup_recognition`, with
`sorry` as its entire proof. There are no new definitions, no dependency repairs,
and no changes to the item's mathematical statement. Only its `lean` record changes.

Sources read: ILO, Exposé VIII, Lemma 3.4.6(i), printed p. 111, including the
paragraph immediately preceding it and its proof (extracted from the supplied PDF);
Stacks `divisors.tex`, Tag 02ND, `lemma-blow-up-integral-scheme`; and
`morphisms.tex`, Tag 035P, `lemma-description-normalization`, including the affine
integral-closure description and proof. ILO identifies the saturated log blowup
with the normalized ordinary blowup; this node is the general finite-normal-model
recognition argument extracted in the node's existing five-step proof. The
declaration docstring carries all five steps and names their DAG dependencies.

Hypothesis-by-hypothesis correspondence:

| Node | Lean |
| --- | --- |
| Integral locally Noetherian scheme X | `{X : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X]` |
| Quasi-coherent ideal J in O_X | `J : X.IdealSheafData`; its affine localization compatibility is exactly quasi-coherent ideal data |
| J nonzero | `hJ : J ≠ ⊥` |
| J finite type | `hfinite : J.toModules.IsQuasiCoherentFiniteType`, the recorded dependency's conjunction for the actual associated ideal module |
| Ordinary blowup B with structure map p | `J.blowup` and `J.blowupMap`, the existing glued blowup, throughout |
| Nonempty dense open U in X | `(U : X.Opens) [Nonempty U] (hUdense : Dense (U : Set X))` |
| J restricted to U is O_U | `hJU : J.comap U.ι = ⊤` |
| Locally Noetherian Y | `{Y : Scheme.{u}} [IsLocallyNoetherian Y]` |
| Finite f : Y -> B | `(f : Y ⟶ J.blowup) [IsFinite f]` |
| Every local ring of Y a normal domain | `hnormal : ∀ y : Y, IsDomain (Y.presheaf.stalk y) ∧ IsIntegrallyClosed (Y.presheaf.stalk y)` |
| V = (p f)^(-1)U dense in Y | `hVdense : Dense ((f ≫ J.blowupMap) ⁻¹' (U : Set X))` |
| V -> U is an isomorphism | `hVU : IsIso ((f ≫ J.blowupMap) ∣_ U)`; this is the actual restricted composite, not an arbitrary isomorphism of the two schemes |

Conclusion-by-conclusion correspondence:

| Node | Lean |
| --- | --- |
| B and Y integral | The two existential witnesses `(_ : IsIntegral J.blowup) (_ : IsIntegral Y)` precede every use of their function fields and of B's normalization |
| f surjective | `Surjective f` |
| Function fields canonically identify with k(X) | `eB : J.blowup.functionField ≅ X.functionField`, `eY : Y.functionField ≅ X.functionField`, together with their two displayed equations on the generic-point spectrum morphisms |
| The field identifications are induced by p and f | `Spec.map eB.hom ≫ J.blowup.fromSpecFunctionField ≫ J.blowupMap = X.fromSpecFunctionField` and `Spec.map eY.hom ≫ Y.fromSpecFunctionField ≫ f = Spec.map eB.hom ≫ J.blowup.fromSpecFunctionField`; contravariance explains the direction of `Spec.map` |
| Every nonempty affine Spec C in B | `∀ (A : J.blowup.Opens) (_hA : IsAffineOpen A) [Nonempty A]`; C is its actual coordinate ring `Γ(J.blowup, A)` |
| Its inverse image is Spec D | The conclusion provides `Nonempty (f ⁻¹ᵁ A)` and `IsAffineOpen (f ⁻¹ᵁ A)`, with D the actual ring `Γ(Y, f ⁻¹ᵁ A)`; no chosen presentation of an affine scheme is required |
| C embeds in D | `Function.Injective (f.app A)` |
| D embeds in the common field | `Function.Injective (Y.germToFunctionField (f ⁻¹ᵁ A) ≫ eY.hom)` |
| These embeddings realize C contained in D contained in k(X) | The displayed equality `f.app A ≫ Y.germToFunctionField (f ⁻¹ᵁ A) ≫ eY.hom = J.blowup.germToFunctionField A ≫ eB.hom` gives the compatible triangle; injectivity of C -> D -> k(X) also gives the embedding C -> k(X) |
| D equals the integral closure of C in k(X) | For every `z : X.functionField`, membership in the image of D is equivalent to `(J.blowup.germToFunctionField A ≫ eB.hom).hom.IsIntegralElem z`; this is exactly the monic-polynomial characterization of the integral closure, with the explicit coefficient map |
| The affine identifications give the unique B-isomorphism Y -> B^nu | `∃! e : Y ≅ J.blowup.normalization, e.hom ≫ J.blowup.fromNormalization = f` |
| No excellence or prior finiteness of normalization | Neither appears in the binders; the normalization is `Scheme.normalization`, not the relative normalization of f |

The generic-point equations specify the field identifications through the given
morphisms, rather than merely asserting that abstractly isomorphic fields exist.
On a nonempty affine of the base they fix the coefficient maps; those maps
determine the fraction-field identifications. The affine statement uses those same
identifications and germs. Uniqueness over B forces the final isomorphism to be the
one given by the integral-closure identifications. The elementwise formulation
uses Mathlib's `RingHom.IsIntegralElem`, defined by a monic polynomial and `eval₂`;
it is the carrier condition of `integralClosure` for precisely that ring map, and
does not introduce a second definition or an arbitrary algebra structure.

Dependency declarations read and reused:

- `Mathlib.AlgebraicGeometry.Properties`: `AlgebraicGeometry.IsIntegral`, whose
  fields are nonemptiness and domain section rings on every nonempty open, and
  its reduced-and-irreducible characterization.
- `Mathlib.AlgebraicGeometry.Noetherian`: `AlgebraicGeometry.IsLocallyNoetherian`,
  the Noetherian section-ring condition on all affine opens.
- `Sheaf.AlgebraicGeometry.CoherentFiniteType`:
  `AlgebraicGeometry.Scheme.Modules.IsQuasiCoherentFiniteType`, the conjunction of
  Mathlib's quasi-coherence and finite-type predicates. Its actual ideal-module
  argument is `Scheme.IdealSheafData.toModules` from
  `WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Module`, the kernel of the
  structure-sheaf map to the closed subscheme's pushforward.
- `WeilConjectures.Blowup.Gluing`:
  `AlgebraicGeometry.Scheme.IdealSheafData.blowup` and `blowupMap`, constructed
  from the existing relative gluing datum.
- `Mathlib.AlgebraicGeometry.Morphisms.Finite`: `AlgebraicGeometry.IsFinite`,
  affine with finite ring maps on affine opens.
- `Mathlib.RingTheory.IntegralClosure.IntegrallyClosed`: `IsIntegrallyClosed`
  and `IsDomain`, used in exactly the dependency's prescribed normal-domain form.
- `WeilConjectures.AlgebraicGeometry.FunctionField`: the recorded node's public
  import of Mathlib's `Scheme.functionField` and `Scheme.germToFunctionField`,
  implementing the node's general integral-scheme clause. The component-product
  definition is not the carrier for an integral scheme.
- `WeilConjectures.Mathlib.AlgebraicGeometry.Normalization`:
  `AlgebraicGeometry.Scheme.normalization` and `fromNormalization`, normalization
  in the function field through `fromSpecFunctionField`.

Proof-dependency imports are included for the already stated blowup integrality,
blowup complement, closedness and finite fibres, affine fraction fields, integral
closure, and morphism-gluing inputs. The recorded normalization-extension
definition is in the same normalization module. The proof dependency
`lem-sfb-finite-normal-cover-normalization` currently has no recorded Lean module
in the read clone; it is named in the proof plan and is not needed to type this
statement. No replacement of that independent theorem is introduced here.

Edge cases checked before writing: J may be the unit ideal, U may be all of X,
and X may be a field spectrum (dimension zero); all are included. J = 0 and empty
U are excluded exactly as in the node. Empty Y is already ruled out by the
specified isomorphism over nonempty U, not by an added hypothesis. Y is allowed
to be disconnected in the hypotheses: its integrality follows from the dense
irreducible open, so no irreducibility assumption is added. There is no
quasi-compactness, separatedness, finite-type-over-a-field, or excellence
restriction. The empty affine open is excluded only from the coordinate-domain
and integral-closure assertion. Nonempty inverse images there are conclusions,
not extra hypotheses. Characteristic is unrestricted. Every scheme and ring
uses the explicitly declared universe u, without a lowered test-object universe.

Searches actually run with the prescribed `msearch.py Q45 <item>` wrapper:

- LeanFinder: `A finite morphism from a normal scheme to an integral blowup which is an isomorphism on a dense open is the normalization`. Eight hits, all for relative normalization of a morphism and its universal property. None states recognition with the blowup, dense-open hypotheses, affine integral closure, and uniqueness.
- Loogle: `AlgebraicGeometry.Scheme.normalization, AlgebraicGeometry.Scheme.Hom.functionFieldMap`. No hits: the service reports unknown identifier `AlgebraicGeometry.Scheme.normalization`. The project supplies this declaration upstream; this is not evidence that the notion is missing locally.
- Grep: `normalization|[Bb]irational`, in `AlgebraicGeometry`. Eighteen hits including Mathlib relative normalization, Zariski's main theorem, and birational rational maps; no exact recognition statement.
- LeanSearch: `A finite birational morphism from a normal scheme to an integral scheme is its normalization in the function field`. Eight hits for relative normalization and `IsFinite`; no exact match.
- Direct `rg` in both `lean/WeilConjectures` and `lean/Sheaf` for the item id,
  `finite.normal`, `normal.*cover`, `blowup.*integral`, `blowup.*recognition`, and
  function-field maps. The item id appears only in consumer proof plans, not in
  an existing declaration. Found and read the existing integral-blowup theorem,
  log-blowup normalization consumer, and generic-point function-field APIs.
- Direct name search in both project roots and Mathlib for
  `FiniteNormalBlowupRecognition|finite_normal_blowup_recognition`: no existing
  declaration or module. No repair note for this item was found in
  `coord/repair-notes`.

There is no `STATEMENT-DISPUTED` issue or source correction.

Validation: the prescribed `scompile.py Q45 lem-trf-finite-normal-blowup-recognition`
accepted the delivered file in both sandbox-module mode and its actual library
module mode, with no compiler diagnostics. The actual library compile took 2.5 s.
All Lean lines are at most 100 characters, all universes and variables are
explicitly bound, and the only proof body is `by sorry`. A parsed comparison with
the original node confirmed that `lean` is the only changed field.
The prescribed `deliver2.py ... --no-push` returned
`OK (dry run): commit 03cf81a289e passes the preflight and compiles; nothing pushed`.

## Second reading by Q45

Independent second reading (maintainer review service, 2026-10-24). It replaces the worker's
own re-check, which was not an independent reading (H11). The Lean statement is unchanged.

Node clauses and their Lean rendering:

- X integral and locally Noetherian: `[IsIntegral X] [IsLocallyNoetherian X]`. These are the
  recorded declarations of def-pc-integral-scheme and pqf-def-locnoeth. Correct.
- J a nonzero, finite-type, quasi-coherent ideal: `J : X.IdealSheafData` (quasi-coherent by
  construction), `hJ : J ≠ ⊥`, and `hfinite : J.toModules.IsQuasiCoherentFiniteType`
  (pqf-def-coherent record; `toModules` = kernel of O_X → i_*O_Z). Correct. The proof dependency
  `isIntegral_blowup_and_isProjectiveBundle` uses the affine `FG` form, which is equivalent for
  a quasi-coherent ideal; this concerns the proof only.
- B = Bl_J X and p: `J.blowup` and `J.blowupMap` (def-nagata-global-blowup,
  WeilConjectures.Blowup.Gluing). Correct.
- U a nonempty dense open with J|_U = O_U: `[Nonempty U]`, `hUdense`, `hJU : J.comap U.ι = ⊤`.
  Mathlib defines `comap` as the kernel of the pullback of the closed subscheme. It is ⊤ exactly
  when U misses V(J), that is, J|_U = O_U. Correct.
- f : Y → B finite, Y locally Noetherian with normal-domain local rings: `[IsFinite f]`,
  `[IsLocallyNoetherian Y]`, and `hnormal` (the inline IsDomain ∧ IsIntegrallyClosed form recorded
  for def-weil-pbc-normal-ring). Correct.
- V dense, and V → U an isomorphism: `hVdense` on the set preimage, and
  `hVU : IsIso ((f ≫ p) ∣_ U)`, which is the actual restricted composite. Correct.
- B and Y integral, f surjective: the existential Prop witnesses (instances for later terms) and
  `Surjective f`. Correct.
- Canonical function-field identifications: `eB` and `eY` pinned by the generic-point equations
  through p and f. A morphism Spec K → X is determined by its point and its residue map, so these
  equations force eB and eY to be the maps induced by p and f. Correct (not arbitrary).
- Affine clause for every nonempty affine Spec C ⊆ B: f⁻¹A is nonempty and affine; C → D is
  injective; D → k(X) is injective; the triangle commutes; and the image of D equals the elements
  of k(X) integral over C via the same germ map (`RingHom.IsIntegralElem`, the Mathlib carrier of
  the integral closure). Correct, neither weaker nor stronger.
- Unique B-isomorphism Y ≃ B^ν: `∃! e : Y ≅ J.blowup.normalization,
  e.hom ≫ fromNormalization = f`. `Scheme.normalization` is the def-sc-normalization record
  (normalization in the function field via fromSpecFunctionField); no finiteness of ν and no
  excellence are assumed. Correct.

Edge cases: J = O_X with U = X, and X = Spec of a field, are included. J = 0 and U = ∅ are
excluded as in the node. Y = ∅ is impossible because V ≅ U ≠ ∅, so no hypothesis is added for it.
Disconnected Y is not excluded by assumption. The empty affine A is excluded only in the affine
clause. All objects use one universe u, with no restriction.

Records: the node is unchanged except `lean`, as diffed against side-live. `lean.statement` is
verbatim in the file. stmt_deps are unchanged, and each cited notion is read from its recorded
declaration. Docstrings carry the source place, `(blueprint: …)` and the five proof steps. The
proof is only `sorry`. There are no new definitions or dependency modules.

Duplicates (H4): no declaration named `finite_normal_blowup_recognition` or
`FiniteNormalBlowupRecognition` exists in the live lean/Sheaf or lean/WeilConjectures. Mathlib
has only relative normalization (`Scheme.Hom.normalization`), which has no recognition statement.
There is no H4 issue.

Findings: no mathematical mismatch. The only change is this section, which replaces the earlier
self-reading.
