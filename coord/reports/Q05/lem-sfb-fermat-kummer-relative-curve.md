## Worker report

The module `Sheaf.AlgebraicGeometry.RelativeFermatKummerCurve` states
`AlgebraicGeometry.RelativeFermatCurve.exists_finite_kummer_cover`, with its sole
proof `sorry`. The five construction helpers in the same namespace are `equation`,
`ideal`, `curve`, `ι`, and `π`. They are specific data introduced by this lemma,
not a second general notion of plane curves, projective space, or normalization.
All have actual definitions. The equation is the difference of the three tensor
powers of the existing coordinate sections of O(1); its zero ideal is used without
radicalization. Thus its subscheme is scheme-theoretically A^l-B^l=C^l.

The node statement, proof and proof dependencies are unchanged. The two added
statement dependencies, `def-pc-zero-scheme` and `def-pc-projective-space-twist`,
are already recorded upstream definitions used to construct the equation's zero
scheme. No new node and no dependency repair is needed.

Hypotheses, individually:

| Node | Lean |
| --- | --- |
| Ground field | `(k : Type u) [Field k]` |
| Base scheme | `(U : Scheme.{u})` |
| Integral base | `[IsIntegral U]` |
| Finite type over the field | `(p : U ⟶ Spec (.of k)) [LocallyOfFiniteType p] [QuasiCompact p]` |
| Normal base, every local ring an integrally closed domain | `hnormal : ∀ z : U, IsDomain (U.presheaf.stalk z) ∧ IsIntegrallyClosed (U.presheaf.stalk z)` |
| Prime l at least 5 | `(l : ℕ) (hl : Nat.Prime l) (hl5 : 5 ≤ l)` |
| l invertible on U | `hinv : IsUnit (l : Γ(U, ⊤))`; a global section is a unit iff it is a unit locally, by gluing inverses |
| Primitive lth root in global functions | `hroot : ∃ ζ : Γ(U, ⊤), IsPrimitiveRoot ζ l`; `IsPrimitiveRoot.iff_orderOf` identifies this with multiplicative order l |

Conclusions, individually:

| Node | Lean |
| --- | --- |
| Closed Fermat curve in P²_U | `equation`, `ideal`, `curve`, and `ι`; the closed-immersion instance is the existing instance on `IdealSheafData.subschemeι` |
| Formula [A:B:C] ↦ [A^l:C^l] is a morphism | existential `ρ`, equality over U, chart preimage equalities `hC` and `hA`, and the two `appLE` identities |
| Finite and surjective | `IsFinite ρ ∧ Surjective ρ` |
| Normal integral total curve | existential `IsIntegral (curve U l)` and the stalkwise domain/integrally-closed conjunction |
| Smooth H-projective over U | `Smooth (π U l) ∧ IsHProjective (π U l)` |
| Geometrically integral curve fibres | `GeometricallyIntegral (π U l)` and `SmoothOfRelativeDimension 1 (π U l)` |
| Every geometric fibre genus (l−1)(l−2)/2, at least 2 | `∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (s : Spec (.of Ω) ⟶ U)`, equality and lower bound for `@Scheme.arithmeticGenus Ω _ (pullback (π U l) s) ⟨pullback.snd (π U l) s⟩` |
| P¹ has function field k(U)(x) with the stated coordinate | `e : RatFunc U.functionField ≃+* (ProjectiveSpace ... U).functionField`, its value on `RatFunc.X` is the germ of `coordRatio ... ⟨1⟩ ⟨0⟩`, and its Spec-map equality identifies the constant-field embedding over U |
| Function field k(U)(x)(a,b), a^l=x and b^l=x−1 | existential algebra over the line's function field, canonical generic-map equality, `FiniteDimensional`, and `∃ a b` with the power equations and `IntermediateField.adjoin ... {a,b} = ⊤` |
| Specified radicals are A/C and B/C | their two equalities with the germs of `(ι U l).app ... (coordRatio ...)` |
| Normalization in that field, by rho | `∃ E : curve U l ≅ P¹_U.normalizationIn (curve U l).functionField`, with `E.hom ≫ P¹_U.fromNormalizationIn ... = ρ` for the constrained algebra |

The existential integrality and nonempty-chart witnesses allow the generic-stalk
and germ interfaces to be used with their required instances. They express
properties of these particular schemes, rather than assumptions on the input.
No arbitrary replacement of the field embedding is allowed: its Spec map must
compose with the line's generic point to the actual composite through rho. The
RatFunc equivalence's Spec map uses `e.symm.toRingHom`, since Spec is contravariant.
The sentence about finite separability and actions in the node only explains
terminology: this particular node introduces no group or action, nor a separate
input extension. Nothing is added as a hypothesis for that sentence.

Dependency declarations were read, including full signatures and docstrings:

| Dependency | Module and declaration used |
| --- | --- |
| def-weil-field | `Mathlib.Algebra.Field.Defs`, `Field` |
| def-pc-integral-scheme | `Mathlib.AlgebraicGeometry.Properties`, `AlgebraicGeometry.IsIntegral` |
| def-weil-finite-type-morphism | `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`, `AlgebraicGeometry.LocallyOfFiniteType`; `Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact`, `AlgebraicGeometry.QuasiCompact` |
| def-weil-finite-integral-morphism | `Mathlib.AlgebraicGeometry.Morphisms.Finite`, `AlgebraicGeometry.IsFinite` |
| def-sbc-smooth-morphisms | `Mathlib.AlgebraicGeometry.Morphisms.Smooth`, `AlgebraicGeometry.Smooth` and `AlgebraicGeometry.SmoothOfRelativeDimension` |
| def-pc-geometrically-irreducible | `Mathlib.AlgebraicGeometry.Geometrically.Integral`, `AlgebraicGeometry.GeometricallyIntegral` |
| def-kun-projective | `WeilConjectures.AlgebraicGeometry.Morphisms.Projective`, `AlgebraicGeometry.IsHProjective` |
| def-sc-function-field | `WeilConjectures.AlgebraicGeometry.FunctionField` imports `Mathlib.AlgebraicGeometry.FunctionField`; its integral-scheme clause expressly uses the existing `Scheme.functionField` and `Scheme.germToFunctionField`; the component-product construction is not copied |
| def-pc-field-extension | `Mathlib.Algebra.Algebra.Defs`, `Algebra` and `algebraMap` |
| def-fin-normalization-extension | `WeilConjectures.Mathlib.AlgebraicGeometry.Normalization`, `AlgebraicGeometry.Scheme.normalizationIn` and `AlgebraicGeometry.Scheme.fromNormalizationIn` |
| def-pc-genus | `WeilConjectures.AlgebraicGeometry.Cohomology.EulerChar`, `AlgebraicGeometry.Scheme.arithmeticGenus` |
| def-nagata-projective-space-base-change | `WeilConjectures.AlgebraicGeometry.ProjectiveSpace`, `AlgebraicGeometry.ProjectiveSpace` |
| def-pc-zero-scheme | `WeilConjectures.AlgebraicGeometry.Modules.ZeroLocus`, `AlgebraicGeometry.Scheme.Modules.Hom.zeroLocus` |
| def-pc-projective-space-twist | `WeilConjectures.AlgebraicGeometry.ProjectiveSpace.Twist`, `AlgebraicGeometry.ProjectiveSpace.twist` |

Additional existing interfaces: `ProjectiveSpace.coordinateSection` from
`WeilConjectures.AlgebraicGeometry.ProjectiveSpace.CoordinateSection`,
`Scheme.Modules.tensorPowSection` from
`WeilConjectures.AlgebraicGeometry.Modules.ClearDenominators`, and
`ProjectiveSpace.coordRatio` from
`WeilConjectures.AlgebraicGeometry.ProjectiveSpace.OfInvertible`.
The source O(1) and each tensor power are invertible, so the zero-locus definition
has precisely its intended invertible-module meaning. It is not applied to a junk
noninvertible sheaf. Public imports expose the statement's notions; ordinary
imports include each already stated proof dependency's module. The new
`lem-sfb-plane-hypersurface-cohomology` has no recorded declaration yet and is
therefore not imported; it remains the explicit DAG proof prerequisite. All nine
proof steps, with their dependency ids, are included in the theorem docstring.

Edge cases checked before writing: integral excludes the empty base; no regularity,
projectivity, algebraic closedness, or perfection is imposed on the base field or
base scheme. A normal base with singularities is allowed. At l=5 the genus formula
is 6. Characteristics 2 and 3 remain allowed when l is invertible; equal
characteristic l is excluded exactly by hinv. The forbidden A=C=0 locus would
force B=0, explaining why the two displayed source charts cover. The second chart
is essential at infinity [1:1:0], where rho has value [1:0]. The points [1:0:1]
prove the source C-chart nonempty. Geometric points range over every algebraically
closed field in the scheme's ambient universe and every map to U, including
nonclosed base points. No independent test universe makes the geometric condition
vacuous. The field-generation condition excludes a further unwanted algebraic
extension. No statement fault or disputed assertion was found.

Searches (2026-10-22; msearch records are also in searches.jsonl):

- msearch leanfinder, `Relative Fermat curve finite Kummer cover of projective line genus smooth normalization`: eight Weierstrass-curve hits, none matching a relative Fermat cover.
- msearch loogle, `Fermat, AlgebraicGeometry.ProjectiveSpace`: zero hits, unknown identifier Fermat.
- msearch grep, `Fermat|fermat|Kummer|kummer` in Mathlib/AlgebraicGeometry: zero hits.
- `rg -n 'Fermat|fermat'` in project AlgebraicGeometry directories: only Artin–Schreier comments using Fermat's identity and `HighGenusEquivariantCover.lean`'s proof docstring referring to this missing prerequisite; no construction or theorem.
- `grep -rn 'lem-sfb-fermat-kummer-relative-curve' lean/WeilConjectures`: no hits.
- `rg -n 'namespace AlgebraicGeometry.RelativeFermatCurve|exists_finite_kummer_cover'` in Mathlib, WeilConjectures and Sheaf: no hits.
- Searches for `coordinateSection`, `tensorPowSection`, `zeroLocus`, and `coordRatio` located the existing interfaces listed above; those are reused.

Validation: scompile.py compiled both the sandbox and actual module successfully
against the live published library (2.5 s and 2.3 s). One prior diagnostic exposed
the contravariant direction of the RatFunc Spec map; it was repaired by using the
inverse ring equivalence. No warning other than the permitted sorry remains.

## Second reading by Q05

A separate second pass reopened the node and the complete module and checked the
two tables above against their actual binders and conjuncts. This is the same
dispatcher worker's second pass: the dispatch expressly forbids starting other
agents, and the maintainer's independent delivery review remains separate.

The pass checked the signs (B^l=x−1), the coordinate order (0=A, 1=B, 2=C; target
0=A^l, 1=C^l), both chart preimages, and the map at infinity. It checked that the
function-field algebra is the one induced by rho and that the normalization
isomorphism commutes with its structure map to the line. The erroneous direction
of the equivalence in the constant-field Spec map was changed to `e.symm` before
the clean compile. It also confirmed that genus uses the geometric fibre's actual
projection to Spec Ω, not an arbitrary Over instance, and that the equation's
closed scheme is not reduced by fiat. No remaining mismatch was found; no
hypothesis or clause was removed and no node statement was changed.
