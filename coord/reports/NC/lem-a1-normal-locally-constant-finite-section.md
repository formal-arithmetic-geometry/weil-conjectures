## Worker report

The module `Sheaf/SecPurity/NormalLocallyConstantFiniteSection.lean` states
`AlgebraicGeometry.exists_finiteEtale_section_of_normal_locallyConstant` with proof `sorry`.
It uses the Mathlib small pro-etale site and the canonical sheaf pullback along each member of a
`Scheme.Cover Scheme.proetalePrecoverage X`.

The hypotheses are rendered as follows. The scheme is `X : Scheme.{u}`. Its nonemptiness and
connectedness are `[Nonempty X]` and `[ConnectedSpace X]`. The Noetherian condition is the pair
of instance hypotheses `[IsLocallyNoetherian X]` and `[CompactSpace X]`, matching locally
Noetherian plus quasi-compact. Normality is the explicit hypothesis
`∀ x : X, IsDomain (X.presheaf.stalk x) ∧ IsIntegrallyClosed (X.presheaf.stalk x)`, so each local
ring is an integral domain integrally closed in its fraction field.

The sheaf of sets is
`F : Sheaf (Scheme.ProEt.topology X) (Type (u + 1))`. Local constancy is the existence of a
pro-etale covering `𝒰`, and for every `i : 𝒰.I₀` a set `S : Type (u + 1)` together with
`Nonempty ((Functor.sheafPullbackConstruction.sheafPullback ... (𝒰.f i) ...).obj F ≅
(constantSheaf ...).obj S)`. This is precisely restriction to the cover member being
isomorphic to the sheafification of the constant presheaf. Local nonemptiness is a second
pro-etale covering `𝒱` and `Nonempty (F.obj.obj (op V))` for each bundled pro-etale object
`V` obtained from `𝒱.f j`; the displayed `Scheme.proetalePrecoverage_le_precoverage_weaklyEtale`
proof supplies its weakly étale structure.

The conclusion is a bundled pro-etale object `Y : Scheme.ProEt X`, whose structural morphism
`Y.hom` satisfies `IsFinite Y.hom ∧ Etale Y.hom ∧ Surjective Y.hom`, and whose section set
`F.obj.obj (op Y)` is nonempty. Thus it states a finite étale surjective morphism and a section
on that cover. The bundled object records the weakly étale site structure without adding a
mathematical hypothesis.

Dependency declarations used in the signature are: `AlgebraicGeometry.Scheme` from
`Mathlib.AlgebraicGeometry.Scheme` (scheme and morphism); `AlgebraicGeometry.IsLocallyNoetherian`
from `Mathlib.AlgebraicGeometry.Noetherian`; `IsDomain`, `IsIntegrallyClosed`, and
`Localization.AtPrime` from `Mathlib.RingTheory.IntegralClosure.IntegrallyClosed` (the normal
local-ring clause); `AlgebraicGeometry.Scheme.ProEt` and
`AlgebraicGeometry.Scheme.proetalePrecoverage` from
`Mathlib.AlgebraicGeometry.Sites.Proetale`; `CategoryTheory.constantSheaf` from
`Mathlib.CategoryTheory.Sites.ConstantSheaf`; `AlgebraicGeometry.IsFinite` and
`AlgebraicGeometry.Etale` from the Mathlib morphism-property modules; and
`AlgebraicGeometry.Surjective` from `Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap`.
The proof-only nodes `lem-a1-proetale-local-system-representability`,
`lem-a1-normal-geometric-cover-components`, and `def-weil-pbc-site-comparison-morphism` are
recorded in the DAG's `proof_deps`; the stage-2 theorem statement does not need to import their
postponed proofs.

Edge cases checked: `Nonempty X` excludes the empty scheme as required; `Scheme.Cover` allows
arbitrary (including infinite) covering families; `S` is an arbitrary set, including the empty
set and singleton; the conclusion selects one finite cover and permits any finite degree,
including degree one. Normality is imposed stalkwise and does not assume finite type or a finite
number of components of the representing cover.

Searches made: `msearch.py ... leanfinder "finite etale surjective cover section locally constant
proetale sheaf normal connected Noetherian scheme"` returned only generic `Scheme.Etale`, site,
and condensed declarations (no match); `msearch.py ... loogle "Scheme.ProEt, constantSheaf,
IsFinite, Etale, Surjective"` returned `0 hits` because `Scheme.ProEt` is source-specific;
`msearch.py ... grep "locally.?constant.*pro.?etale|normal.*finite.?etale|finiteEtale.*section"
AlgebraicGeometry` returned no hits. Direct `rg` over `WeilConjectures` found no declaration or
item-name occurrence. `tools/blueprint_refs.py search lem-a1-normal-locally-constant-finite-section`
returned zero blueprint nodes. The DAG search found no duplicate declaration of this statement.

## Second reading by NC

I reread the node and module side by side. The four scheme hypotheses are represented by the
nonempty, connected, locally Noetherian, and quasi-compact instances. The stalkwise conjunction
has both domain and integral-closure clauses. The sheaf is set-valued on exactly `X.ProEt`; the
first cover gives one constant-sheaf isomorphism for every member, and the second gives one
section for every member. The conclusion quantifies one bundled object over `X`, retains all three
finite/étale/surjective properties, and asserts its section set is nonempty. No finiteness of the
covering index or of the constant sets was added, and no normality or local-nonemptiness clause
was dropped. The statement was compiled cleanly with `scompile.py`; only the theorem proof is
postponed by `sorry`.
