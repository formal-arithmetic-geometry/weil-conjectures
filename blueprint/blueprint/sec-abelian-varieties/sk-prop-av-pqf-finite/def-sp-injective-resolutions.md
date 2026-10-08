+++
id = "def-sp-injective-resolutions"
kind = "definition"
title = "Injective objects and injective resolutions"
order = 500
uses = ["def-sp-grothendieck-abelian"]
+++
An object $I$ of an *abelian category* is *injective* if for every
monomorphism $M\hookrightarrow N$, the restriction
$\operatorname{Hom}(N,I)\to\operatorname{Hom}(M,I)$ is surjective. Here
$\operatorname{Hom}(-,I)$ is contravariant. An *injective resolution* of an
object $X$ of an abelian category with enough injectives is a bounded-below
cochain complex $X\longrightarrow I^\bullet$ of injective objects whose
cohomology is concentrated in degree zero, where it equals $X$.
