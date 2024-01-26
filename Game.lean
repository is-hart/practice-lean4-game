import Game.Metadata

import Game.Levels.Tutorial
import Game.Levels.EvenOdd
import Game.Levels.ThreevenThrodd

-- Here's what we'll put on the title screen
Title "The Threeven Game"
Introduction
"
You've heard of even and odd numbers, but have you met threeven, throver, and thrunder?
"

Info "
We made this game and it's dope
"

/-! Information to be displayed on the servers landing page. -/
Languages "English"
CaptionShort "The Threeven Game"
CaptionLong "You should play this game bc its cool."
-- Prerequisites "" -- add this if your game depends on other games
-- CoverImage "images/cover.png"

/-! Build the game. Shows warnings if it found a problem with your game. -/
MakeGame
