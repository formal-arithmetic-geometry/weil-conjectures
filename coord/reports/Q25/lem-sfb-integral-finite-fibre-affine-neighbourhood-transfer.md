## Worker report

The module `Sheaf.AlgebraicGeometry.IntegralFiniteFibreAffineNeighbourhoodTransfer`
states `AlgebraicGeometry.exists_affineOpen_iff_preimage_of_integral_surjective_finite_fibres`.
Its only theorem has proof `sorry`. No definition, extra node, dependency repair or
statement correction is needed. The original node is changed only in `lean`.

Clause-by-clause correspondence:

- Schemes Y and Z: `{Y Z : Scheme.{u}}`; the common arbitrary universe is the universe
  of Mathlib's category of schemes, without further size assumptions.
- Z locally Noetherian: `[IsLocallyNoetherian Z]`. There is no such binder on Y.
- The given morphism: `(q : Y ⟶ Z)`.
- Integral: `[IsIntegralHom q]`, using the declaration explicitly recorded by the
  finite/integral dependency, rather than imposing `[IsFinite q]`.
- Surjective: `[Surjective q]`, Mathlib's condition that the underlying map is surjective.
- Finite underlying fibres: `(hfinite : ∀ z : Z, (q ⁻¹' {z}).Finite)`. This is literal
  finiteness of the inverse image of every point, with no finite-type or flatness hypothesis.
- Every finite subset: `(E : Set Z) (hE : E.Finite)`; no nonemptiness condition.
- An affine open of Z containing E: `∃ U : Z.Opens, IsAffineOpen U ∧ E ⊆ (U : Set Z)`.
- Equivalence: `↔`, retaining both implications.
- An affine open of Y containing the entire inverse image:
  `∃ V : Y.Opens, IsAffineOpen V ∧ q ⁻¹' E ⊆ (V : Set Y)`.
- Affine means spectrum of a commutative ring: Mathlib `IsAffineOpen U` is `IsAffine U`;
  `Scheme.isoSpec` identifies every such scheme with `Spec Γ(U, ⊤)`. This is the usual
  affineness notion, not a property of a chosen chart or a strengthened embedding condition.

Statement dependencies read and used:

- `def-pc-scheme`: `AlgebraicGeometry.Scheme`, `AlgebraicGeometry.Scheme.Hom`, in
  `Mathlib.AlgebraicGeometry.Scheme`.
- `pqf-def-locnoeth`: `AlgebraicGeometry.IsLocallyNoetherian`, in
  `Mathlib.AlgebraicGeometry.Noetherian`. Its every-affine-open definition is the recorded
  equivalent presentation of the existence of a Noetherian affine cover.
- `def-weil-finite-integral-morphism`: `AlgebraicGeometry.IsIntegralHom`, in
  `Mathlib.AlgebraicGeometry.Morphisms.Integral`, publicly reexported by its recorded
  module `Mathlib.AlgebraicGeometry.Morphisms.Finite`. The actual class extends
  `IsAffineHom` and requires integral maps on every affine open's sections.
- `def-weil-affine-spectrum`: `AlgebraicGeometry.Spec` and `Spec.map`, in
  `Mathlib.AlgebraicGeometry.Scheme`; affineness is expressed through Mathlib's
  `IsAffineOpen`, `IsAffine` and `Scheme.isoSpec` in `Mathlib.AlgebraicGeometry.AffineScheme`.

These recorded modules are public imports. The statement also uses Mathlib's `Set.Finite`
and the underlying point map of a scheme morphism, and `AlgebraicGeometry.Surjective`
from `Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap` (publicly available through the
statement imports). No private copy of a dependency notion is introduced.

The module docstring names both original sources. The theorem docstring reproduces all nine
proof steps, including semilocalization, prime avoidance, the closed-image argument,
descent of a flat monomorphism, affine descent, and the final principal open. Published proof
dependencies are imported without `public`. In particular the affine-target theorem uses
`WeilConjectures.AlgebraicGeometry.SurjectiveUniversallyClosedAffineTarget`, not a duplicate
Sheaf module. Two proof dependencies currently have neither Lean records nor Mathlib
matches and hence have no import: `lem-sfb-integral-descent-flat-monomorphism-subset` and
`lem-sfb-flat-monomorphism-quasiaffine-neighbourhood`. They are not needed to type this
statement. Both remain in the unchanged DAG proof and theorem docstring for stage 3.

Source check: I read the primary scan's proposition on PDF page 52 (index 51), printed p.55.
It states precisely local Noetherianity of the target, an integral surjective morphism with
set-theoretically finite fibres, and the equivalence for a finite set and its inverse image.
See [Anantharaman, Proposition 4.1.3 (OCR 4.1.5)](https://www.numdam.org/article/MSMF_1973__33__5_0.pdf).
No assumptions from the preceding discussion of group schemes or traits are imported into
this standalone proposition. The Raynaud proof follows the node's accepted nine-step split;
its local archive is marked WANTED, so I do not claim to have reread that scan.

Edge cases checked mathematically before writing:

- E empty: both witnesses can be the empty open, an affine scheme isomorphic to Spec(0).
  `Set.Finite` permits this case; no ring is required to be nontrivial.
- Z empty: surjectivity and the existence of q force Y empty; the same witnesses work.
- q the identity: both clauses are the same assertion about a finite set.
- Singleton E: the upstairs condition contains the whole fibre, not just a chosen lift.
- Nonflat finite cover: the reduction Spec(k) → Spec(k[ε]/(ε²)) is a finite integral
  surjection and is not flat; there is no Flat binder here.
- Integral covers need not be finite: Spec of an infinite algebraic field extension over
  a field has one underlying fibre point and satisfies the binders.
- Y need not be locally Noetherian: an infinite square-zero extension of a field is integral
  over the field, has one point, and is not Noetherian. It is allowed here.
- Nonaffine target: nothing assumes Z or Y affine, so the equivalence is not trivialized.

Searches performed (2026-10-24), all before introducing the theorem:

- `msearch.py ... leanfinder`: "An integral surjective morphism with finite underlying fibres
  onto a locally Noetherian scheme transfers existence of affine neighbourhoods of finite
  sets". Eight hits on IsFinite, finite sections and finite type; no exact equivalence.
- `msearch.py ... leansearch`: "Affine neighbourhood of a finite set descends along an
  integral surjective morphism with finite underlying fibres". Eight hits on IsFinite,
  affine-morphism properties and fibre finiteness; none states this equivalence.
- `msearch.py ... loogle`: `"IsIntegralHom", "IsAffineOpen"`. Zero hits.
- `msearch.py ... grep`, Mathlib AlgebraicGeometry:
  `integral.*affine.*neigh|affine.*neigh.*integral|finite.*subset.*affine`. Zero hits.
- `rg` in `lean/WeilConjectures` and `lean/Sheaf`, first for affine neighbourhoods, then for
  `integral.*[Nn]eighbour|[Nn]eighbour.*integral|finite_fibre.*affine|finiteFiber.*affine`:
  related results (integral pointed etale models, birational integral neighbourhoods,
  Ferrand pushouts) but no finite-set equivalence. Exact node-id search in upstream:
  no match. The proposed full theorem name is absent from both trees and Mathlib.

Validation: the prescribed `scompile.py Q25 <item> <file>` compiled both the sandbox and
library module successfully, with no errors or warnings other than the permitted sorry
warning (the wrapper printed no diagnostics). No local Lean or global build was run.

## Second reading by Q25

I reread the node and final signature clause by clause. The fibre hypothesis is on the
underlying singleton preimages for every target point; the conclusion uses the preimage
of E, not its image, and requires containment of every point. Both affine witnesses are
opens of the stated schemes. Only Z has local Noetherianity. The binder `hE` allows the
empty set. No extra finite, flat, separated or Noetherian condition was introduced. The
nine proof steps are present in the theorem docstring. No mismatch or correction was found.
This is a worker self-check, not a claimed independent second agent: the dispatcher forbids
starting other agents, and the maintainer supplies the independent delivery review.
