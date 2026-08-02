import Verso
import VersoManual
import VersoBlueprint
import WeilConjectures
import WeilConjecturesBlueprint.TexPrelude

open Verso.Genre
open Verso.Genre.Manual
open Informal

#doc (Manual) "Étale cohomology" =>

The realization layer needs the small étale site, torsion and ℓ-adic
coefficients, stalks and exactness, and the Frobenius dictionary. The
repository already contains a first block of site-theoretic infrastructure:
the lower shriek for localized sites, which realizes extension by zero at
the level of sheaf categories and will support the localization triangles of
the six-operation fragment.

:::group "group:etale-sites"
Site-theoretic infrastructure: localization of sites, lower shriek, and the
open-localization property.
:::

# Localization and lower shriek

:::definition "def:localization-lower-shriek" (parent := "group:etale-sites") (lean := "CategoryTheory.GrothendieckTopology.localizationLowerShriek")
Let $`(C, J)` be a site, $`f \colon V \to U` a morphism of $`C`, and $`A` a
coefficient category. The *localization lower shriek*
$`j_! \colon \mathrm{Sh}(J/V, A) \to \mathrm{Sh}(J/U, A)`
is the left adjoint of the restriction functor along the slice functor
$`\mathrm{Over}(f) \colon C/V \to C/U`, constructed as left Kan extension
on presheaves followed by sheafification. It is left adjoint to the
localization restriction $`j^*` (formalized as
`localizationLowerShriekAdjunction`).
:::

:::definition "def:open-localization" (parent := "group:etale-sites") (uses := "def:localization-lower-shriek") (lean := "CategoryTheory.GrothendieckTopology.IsOpenLocalization")
A morphism $`f \colon V \to U` is an *open localization* for $`J` if the
induced map of sheafified representables is a monomorphism. For such $`f`
(in particular for monomorphisms), the unit of the adjunction
$`j_! \dashv j^*` is an isomorphism and $`j_!` is fully faithful — the
sheaf-theoretic form of extension by zero along an open immersion. For the
small étale site of a scheme this captures open subschemes, and the
composition and identity isomorphisms for $`j_!` are also formalized.
:::

Future nodes of this chapter: the small étale site of a scheme, geometric
points and stalk exactness, constructible and lisse sheaves, the
Weil-sheaf category (Frobenius descent data), the ℓ-adic coefficient
formalism (normalized Artin–Rees systems — never "inverse limits are
exact"), and the Frobenius dictionary pinned by the executable
normalization tests of the zeta chapter.
