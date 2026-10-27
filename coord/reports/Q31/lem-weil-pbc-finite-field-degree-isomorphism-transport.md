## Worker report

The module states `AlgebraicGeometry.Scheme.Hom.finite_field_degree_isomorphism_transport`, with its entire proof postponed by `sorry`. There are no new notions, dependency repairs, or statement corrections. The item's other JSON fields are unchanged.

Hypotheses and clauses, in statement order:

- Fields K and L: `{K L : Type u} [Field K] [Field L]`. A field isomorphism is the ring equivalence `φ : K ≃+* L`; `Spec.map (CommRingCat.ofHom φ.toRingHom)` is the prescribed contravariant spectrum map j. No characteristic restriction.
- Schemes and their structure maps: `{Z T : Scheme.{u}}`, `h : Z ⟶ Spec (CommRingCat.of K)` and `q : T ⟶ Spec (CommRingCat.of L)`. A common size universe is the ambient scheme category's universe; any pair of fields can be put in a common universe. The index universe w is independent.
- The scheme isomorphism: `u : T ≅ Z`. The square is `comm : u.hom ≫ h = q ≫ Spec.map (CommRingCat.ofHom φ.toRingHom)`, exactly h composed with u equals j composed with q.
- A and B are literally `Γ(Z, ⊤)` and `Γ(T, ⊤)`. Their scalar maps α and β are `((Scheme.ΓSpecIso (CommRingCat.of K)).inv ≫ h.appTop).hom` and the corresponding L/q expression. These are the defining maps of the existing `h.ΓAlgebra` and `q.ΓAlgebra`.
- The conclusion supplies `e : Γ(Z, ⊤) ≃+* Γ(T, ⊤)` with `e.toRingHom = u.hom.appTop.hom`. This equality fixes the equivalence to the canonical pullback u*, rather than an arbitrary isomorphism. The existence is a proposition, not data used to define a new object.
- The equality of ring homomorphisms `e.toRingHom.comp α = β.comp φ.toRingHom` is precisely u* composed with α equals β composed with φ.
- The next conjunct quantifies over every `a : K` and `v : Γ(Z, ⊤)` and states `e (α a * v) = β (φ a) * e v`.
- For every `I : Type w` and family `v : I → Γ(Z, ⊤)`, the next conjunct equates existence of a `Module.Basis` with vectors v to existence of a `Module.Basis` with vectors e(v). `@Algebra.toModule ... h.ΓAlgebra` and its q counterpart explicitly fix the module instances; no arbitrary scalar actions or extra assumptions enter. Existence of a basis structure with those vectors expresses exactly that this particular family is a basis.
- `IsFinite h ↔ IsFinite q` renders both directions of finiteness transport without assuming finiteness initially.
- `IsFinite h → h.finrankΓ = q.finrankΓ` renders degree equality when the equivalent finiteness conditions hold. The existing `finrankΓ` unfolds to `Module.finrank` with exactly the above `ΓAlgebra` instances. By the preceding iff, requiring h finite is exactly requiring either map finite; no clause is lost.

Dependency declarations used, read in their source modules:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme`, `Scheme.Hom`, `Spec`, `Spec.map`, and `Scheme.ΓSpecIso`; the proof also uses `Scheme.ΓSpecIso_inv_naturality` and functoriality of `appTop`. These provide the scheme and affine-spectrum nodes and the exact Mathlib match of lem-weil-pbc-spec-map-global-sections.
- `Mathlib.AlgebraicGeometry.Morphisms.Finite`: `AlgebraicGeometry.IsFinite` (extends IsAffineHom and requires finite ring maps on affine opens); proof ingredients include finite composition and `Scheme.Hom.finite_appTop`.
- `WeilConjectures.AlgebraicGeometry.FiberDegreeBound`: recorded `Scheme.Hom.BoundsFiberDegrees` and `HasUniversallyBoundedFibers`, which use `finrankΓ`. Its public dependency `WeilConjectures.AlgebraicGeometry.Morphisms.FiberDegree` supplies the actual `Scheme.Hom.ΓAlgebra` and `finrankΓ`. Both definitions were read in full; no second degree or scalar structure is defined.
- `Mathlib.LinearAlgebra.Dimension.Finrank`: recorded `Module.finrank`. `Algebra.finrank_eq_of_equiv_equiv` is a reusable dimension ingredient but does not state the entire item.
- `Mathlib.LinearAlgebra.Basis.Defs`: `Module.Basis`, represented by a linear equivalence to finitely supported coordinates, used for arbitrary indexed bases.
- Plain proof imports include `Mathlib.Geometry.RingedSpace.LocallyRingedSpace` (recorded `LocallyRingedSpace.Hom`), `Mathlib.AlgebraicGeometry.AffineScheme` (`Scheme.isoSpec` and its naturality), `Mathlib.AlgebraicGeometry.Morphisms.Affine` (`isAffine_of_isAffineHom`), and `Mathlib.RingTheory.Finiteness.Defs` (`RingHom.finite_algebraMap`). All already stated proof dependencies are available through these imports and the public imports.

Edge cases checked before and after writing:

- Empty schemes: global sections form the zero ring, the empty family is a basis of the zero vector space, and both degrees are zero. No Nonempty or nonzero-algebra condition is imposed.
- Empty index set: admitted without a finiteness or nonemptiness instance; it is a basis exactly in the zero-space case on both sides.
- Infinite index sets and nonfinite schemes: basis and semilinearity clauses remain unconditional. The degree clause alone requires finiteness, so the convention finrank = 0 in infinite dimension is not presented as a degree.
- Identity isomorphisms give the expected identities. A nontrivial field automorphism, such as complex conjugation, is admitted by the φ-semilinear formula; ordinary K-linearity is not imposed.
- Nonreduced finite algebras such as K[ε]/(ε²) retain vector-space degree two, rather than counting points.
- No separatedness, affine, finite-type, finite-dimensionality, or nonemptiness assumption was added. Affineness and finite dimension in the finite case belong to the proof dependencies.

Source read: `literature/stacks-project/morphisms.tex`, paragraph before definition-universally-bounded (Tag 03J4), and lemma-characterize-universally-bounded (Tag 03J5) with its proof. Degree is explicitly vector-space dimension. The DAG supplies the auxiliary compatible-isomorphism argument in five steps; the theorem docstring reproduces each step and names its inputs. The source agrees with the node. No STATEMENT-DISPUTED fault was found.

Searches made (2026-10-22; full wrapper evidence in sandbox searches.jsonl):

- msearch.py loogle, query `Algebra.finrank_eq_of_equiv_equiv`: 1 hits; top results Algebra.finrank_eq_of_equiv_equiv. No hit states all clauses of this item.
- msearch.py grep, query `finrankΓ|finrank_eq_of_equiv_equiv|basis.*[Ii]so` in AlgebraicGeometry: 25 hits; top results Mathlib/AlgebraicGeometry/Properties.lean, Mathlib/AlgebraicGeometry/Properties.lean, Mathlib/AlgebraicGeometry/ProjectiveSpectrum/Topology.lean, Mathlib/AlgebraicGeometry/EffectiveEpi.lean, Mathlib/AlgebraicGeometry/EffectiveEpi.lean, Mathlib/AlgebraicGeometry/Cover/Open.lean, Mathlib/AlgebraicGeometry/QuasiAffine.lean, Mathlib/AlgebraicGeometry/FunctionField.lean. No hit states all clauses of this item.
- msearch.py leanfinder, query `Compatible isomorphisms of schemes over isomorphic fields preserve finiteness and bases of global sections and finite degree`: 8 hits; top results AlgebraicGeometry.IsFinite.instOfIsIsoScheme, AlgebraicGeometry.Scheme.SpecToEquivOfField_eq_iff, RingHom.EssFiniteType.respectsIso, RingHom.finiteType_respectsIso, AlgebraicGeometry.finite_appTop_of_universallyClosed, AlgebraicGeometry.Scheme.residueFieldCongr_trans, AlgebraicGeometry.Scheme.instIsOverMapHomCommRingCatResidueFieldCongr, AlgebraicGeometry.Scheme.SpecToEquivOfField. No hit states all clauses of this item.
- msearch.py leansearch, query `A commuting isomorphism of schemes over isomorphic fields induces a semilinear isomorphism of global sections preserving arbitrary bases and finiteness`: 8 hits; top results AlgebraicGeometry.Scheme.Hom.instIsIsoCommRingCatApp, AlgebraicGeometry.Scheme.Modules.instIsIsoAbApp, AlgebraicGeometry.Scheme.inv_appTop, AlgebraicGeometry.Scheme.Hom.appIso, AlgebraicGeometry.arrowIsoΓSpecOfIsAffine, AlgebraicGeometry.Scheme.isoSpec, AlgebraicGeometry.instIsIsoSchemeMapOfCommRingCat, AlgebraicGeometry.arrowResLEAppIso. No hit states all clauses of this item.
- `rg` in `lean/WeilConjectures` and `lean/Sheaf` for finite-field degree/isomorphism transport and `finrank_eq_of_equiv_equiv` found `Scheme.Hom.finrankΓ_eq_of_iso` in the existing FiberDegree module and dimension applications. The former states degree equality only, not the canonical ring map, scalar compatibility, arbitrary basis equivalence, and finiteness iff. It is therefore an ingredient, not an exact existing match.
- `grep -rn` for the item id in `lean/WeilConjectures` found no match. Searches of `dag/lean_names_upstream.json`, `lean/WeilConjectures`, and `lean/Sheaf` for the new declaration name found no collision.

Validation: the prescribed scompile.py server check compiled the module in sandbox and library modes cleanly. Only the expected postponed theorem is present. All universes and variables are explicitly bound; `autoImplicit` is disabled. No local notation, local instance, private definition, let binder, or copied notion is used.

## Second reading by Q31

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
