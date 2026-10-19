## Worker report

The module `Sheaf.AlgebraicGeometry.AffineFanHomUniversal` defines the canonical section
pullback `AlgebraicGeometry.FineFan.affinePullback` and states
`AlgebraicGeometry.FineFan.affine_hom_universal`, with its sole proof `sorry`.
The node's natural-language statement, dependencies and proof are unchanged. The helper
belongs to this universal property and uses real data, with no choice of a morphism.

Hypotheses and clauses, compared with the node and ILO VIII 3.1.8(ii), printed p.99:

- A topological space with a sheaf of commutative monoids is
  `T : SheafedSpace CommMonCat.{u}`. This is an arbitrary sheafed space, not a fine fan:
  no local affine charts, finiteness, integrality or saturation are assumed for T.
- Sharp stalks are exactly `∀ x : T, IsSharp (stalk T.presheaf x)`.
  The dependency uses multiplicative notation; `1` means the node's additive `0`.
- The fine sharp monoid is `P : Type u`, `[CommMonoid P]`, `hP : IsFine P`,
  `sP : IsSharp P`. `IsFine` includes finite generation and injectivity into group
  completion. No saturation or torsion-freeness is imposed.
- The affine target `S(P)` is the recorded `affine P`, not a replacement ring spectrum.
  It uses the prime spectrum with the empty ideal, the local-fraction monoid sheaf,
  and the sheafification of its quotient by units.
- A morphism in the node is `{f : T ⟶ affine P // IsLocalMorphism f}`.
  Mathlib's sheafed-space morphism consists of a continuous map and compatible maps
  on sections over inverse images of opens. By the inverse-image/direct-image
  adjunction this is precisely the specified inverse-image sheaf homomorphism.
  `IsLocalMorphism` requires `IsLocalHom` for every actual stalk map, i.e. inverse
  image of the units equals the units. It is not mere preservation of units.
- Pullback of the canonical sections is literally
  `(SheafedSpace.Γ.map f.op).hom.comp (affineSection P)`.
  The canonical map `affineSection P` already contains the monoid quotient and both
  sheafification units; no arbitrary global-sections identification is assumed.
- The first conjunct is `Function.Bijective` of this map on local morphisms, with
  codomain `P →* T.presheaf.obj (op ⊤)`, exactly the asserted natural bijection.
- Naturality in `(T,A)` is the second conjunct: for sharp T and T' and local maps
  `k : T' ⟶ T` and `f : T ⟶ affine P`, pullback along `k ≫ f` equals the composite
  of the section pullback of f with `Γ(k)`. The raw section map is defined for all
  sheafed-space morphisms, so writing this equation requires no extra locality
  assumption on the composite or independently chosen composition operation.
- Naturality in P is the third conjunct, for every fine sharp Q and every homomorphism
  `v : P →* Q`. There is a unique local `g : affine Q ⟶ affine P` pulling back each
  canonical section p to the canonical section v(p), and for every local
  `f : T ⟶ affine Q` from a sharp space, pullback along `f ≫ g` is
  `(affinePullback f).comp v`. The unique g is the induced spectrum morphism;
  it is neither an arbitrary supplied map nor an added premise. Its existence and
  uniqueness follow by the first clause applied to the sharp affine space of Q.
  Together with the canonical-section formula, uniqueness also gives identity and
  composition compatibility. Thus this expands the node's two-variable naturality.

Dependency declarations read and used, all from
`Sheaf.AlgebraicGeometry.FineFanBlowup`:
`IsFine`, `IsSharp`, `affine`, `stalk`, `IsLocalMorphism`, `stalkMap`, and `affineSection`.
Read the complete defining signatures and docstrings, including the actual local fraction
and sharpened sheaf constructions and the canonical section construction. The underlying
morphism and global-sections functor are Mathlib's `SheafedSpace` and `SheafedSpace.Γ`
from `Mathlib.Geometry.RingedSpace.SheafedSpace`.
The proof dependency `lem-trf-affine-fan-localization-sections` has no Lean declaration
or module yet, so no import for it can be added. Its node remains a proof dependency;
its role in the seven proof steps is included explicitly in the theorem docstring.

Edge cases checked: T empty (sharpness is vacuous, global sections form the terminal
monoid, and there is exactly one morphism); P trivial (the affine spectrum has one point
and trivial sharp sheaf); the empty prime and generic point are retained; fine sharp
nonsaturated and fine sharp monoids with torsion in the completion are allowed; T need
not itself be a fan, integral, or have a finite affine cover. Identity and arbitrary
monoid homomorphisms v are included, without requiring v to be local. All universes and
variables are bound explicitly. The shared universe u is the dependency's universe
convention and can be chosen to contain all spaces and monoids in an instance.

Searches were made with msearch.py and recorded automatically in sandbox searches.jsonl:

- LeanFinder: `Morphisms from a sharp monoidal space to the spectrum of a fine sharp
  monoid are naturally equivalent to monoid homomorphisms into global sections`.
  Eight hits concern the ring-valued `Spec.homEquiv` and Gamma-Spec adjunctions.
  These are locally ringed spaces and commutative rings, not monoid spectra.
- LeanSearch: `sharp monoid spectrum global sections universal property natural bijection`.
  Eight hits concern Gamma-Spec and the universal property of monoid algebras;
  none states this universal property for sharp monoidal spaces.
- Loogle: `IsLocalHom, MonoidHom`. Five hits provide the local-monoid-map API and
  its composition properties, not this universal property.
- msearch grep: `affine.*[Hh]om|monoid.*spectrum|[Mm]onoidalSpace`.
  Twenty-five unrelated hits on affine linear maps and ring factorization.
- Direct rg on the source project's WeilConjectures tree for the item id, KatoFan,
  MonoidSpectrum and the proposed declaration names returned no declaration. The upstream
  name index has no FineFan universal property. Direct rg on lean/Sheaf found the owning
  FineFanBlowup definitions, which are reused, and unrelated scheme affine-pullback lemmas;
  no duplicate statement or helper with these full names was found.
- Read Mathlib's global-sections signatures and Gamma-Spec adjunction definitions to
  distinguish the existing ring statement from the node's monoid statement.

The local PDF was opened with pdftotext: PDF pages 104--105 contain printed pp.98--99,
including definitions 3.1.3 and 3.1.6 and the entire statement and proof of 3.1.8(ii).
No source discrepancy or disputed statement was found. No new nodes, dependency repairs,
or statement correction are needed.

Validation: scompile.py compiled the sandbox probe and the actual library module separately,
with no errors or warnings. The dependency is a legacy Lean file, so this module uses the
same ordinary-import format: an initial module-system version was rejected because a
`module` cannot import this non-`module` dependency. Switching the new file's format
resolved that compatibility issue without changing any dependency or mathematical object.

## Second reading by Q64

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
