10 REM SPAWN: two random circles; every collision spawns a new one
20 REM --- Screen setup: fixed 400x300 window, white on black ---
30 x$ = "n" : r = 14
40 SCREENSIZE 1000,700
50 COLOR 7, 0
60 CLS
70 REM --- Circle constants and arrays (position, velocity, speed, color) ---
80 MAXC = 1000
90 DIM CX(1000)
100 DIM CY(1000)
110 DIM VX(1000)
120 DIM VY(1000)
130 DIM SP(1000)
140 DIM CL(1000)
150 dim cxo(1000), cyo(1000)
160 N = 0
170 REM --- Seed the first two circles at non-overlapping random spots ---
180 N = N + 1
190 I = N
200 CX(I) = R + 1 + (XSZ() - 2*R - 2) * RND
210 CY(I) = R + 1 + (YSZ() - 2*R - 2) * RND
220 IF I = 1 THEN 240
230 IF (CX(I) - CX(1))^2 + (CY(I) - CY(1))^2 < (2*R + 4)^2 THEN 200
240 REM Give the new circle a random speed (1-5), direction, and color
250 sp(i)=15
260 A = 6.283185 * RND
270 VX(I) = SP(I) * COS(A) : VY(I) = SP(I) * SIN(A)
280 CL(I) = 1 + INT(15 * RND)
290 REM Once two circles exist, hand off to the main loop; else keep seeding
300 IF N >= 2 THEN 320
310 GOTO 180
320 REM === Main loop: move, bounce off walls, resolve collisions, draw ===
330 REM -- Move every circle by its velocity, one frame at a time --
340 FOR I = 1 TO N
350 cxo(i)=cx(i) : cyo(i)=cy(i)
360 CX(I) = CX(I) + VX(I)
370 CY(I) = CY(I) + VY(I)
380 REM -- Bounce off the left wall (reflect velocity, clamp position) --
390 IF CX(I) <= R THEN VX(I) = -VX(I) : CX(I) = 2*R
400 REM -- Bounce off the right wall --
410 IF CX(I) >= XSZ() - 1 - R THEN VX(I) = -VX(I) : CX(I) = XSZ() - 2*R
420 REM -- Bounce off the top wall --
430 IF CY(I) <= R THEN VY(I) = -VY(I) : CY(I) = 2*R
440 REM -- Bounce off the bottom wall --
450 IF CY(I) >= YSZ() - 1 - R THEN VY(I) = -VY(I) : CY(I) = YSZ() - 2*R
460 NEXT I
470 REM === Collisions: for every overlapping pair, bounce them apart, ===
480 REM === then (under the cap) spawn one new circle near the midpoint ===
490 NN = N
500 FOR I = 1 TO NN
510 FOR J = I + 1 TO NN
520 DX = CX(J) - CX(I) : DY = CY(J) - CY(I)
530 REM -- No collision if farther apart than 2R --
540 IF DX*DX + DY*DY >= 4*R*R THEN 970
550 REM -- Overlapping: build a unit vector from I toward J (D = distance) --
560 D = SQR(DX*DX + DY*DY)
570 IF D < .001 THEN DX = 1 : DY = 0 : D = 1
580 UDX = DX/D : UDY = DY/D
590 REM -- Project both velocities onto the collision axis --
600 VI = VX(I)*UDX + VY(I)*UDY
610 VJ = VX(J)*UDX + VY(J)*UDY
620 REM -- Elastic bounce: swap the along-axis components (equal masses) --
630 VX(I) = VX(I) + (VJ - VI)*UDX : VY(I) = VY(I) + (VJ - VI)*UDY
640 VX(J) = VX(J) - (VJ - VI)*UDX : VY(J) = VY(J) - (VJ - VI)*UDY
650 REM -- Push the pair apart so they no longer overlap --
660 OV = (2*R - D)/2 + .5
670 CX(I) = CX(I) - OV*UDX : CY(I) = CY(I) - OV*UDY
680 CX(J) = CX(J) + OV*UDX : CY(J) = CY(J) + OV*UDY
690 REM -- At the circle cap, stop spawning; else place a new circle --
700 IF N >= MAXC THEN 970
710 REM -- New circle spawns at the pair's midpoint, pushed out 2R+8 --
720 MX = (CX(I) + CX(J))/2 : MY = (CY(I) + CY(J))/2
730 T = 0
740 T = T + 1
750 IF T > 80 THEN 970
760 REM -- Random spawn angle A (0 to 2*pi); retry if it is rejected below --
770 A = 6.283185 * RND
780 SX = MX + (2*R + 8) * COS(A) : SY = MY + (2*R + 8) * SIN(A)
790 REM -- Reject candidate spots that fall outside the play area --
800 IF SX < R + 1 OR SX > XSZ() - 1 - R THEN 740
810 IF SY < R + 1 OR SY > YSZ() - 1 - R THEN 740
820 OK = 1
830 FOR C = 1 TO N
840 REM -- Reject if too close to any circle, or not moving away from it --
850 IF (SX - CX(C))^2 + (SY - CY(C))^2 < (2*R + 4)^2 THEN OK = 0
860 IF COS(A)*(SX - CX(C)) + SIN(A)*(SY - CY(C)) < 0 THEN OK = 0
870 NEXT C
880 IF OK = 0 THEN 740
890 REM -- Accepted: record the new circle's position, speed, direction, color --
900 N = N + 1
910 CX(N) = SX : CY(N) = SY
920 sp(n)=15
930 IF SP(N) = SP(I) OR SP(N) = SP(J) THEN SP(N) = SP(N) + .5
940 VX(N) = SP(N) * COS(A) : VY(N) = SP(N) * SIN(A)
950 CL(N) = 1 + INT(15 * RND)
960 REM -- Next pair; the outer FOR resumes the scan of remaining pairs --
970 NEXT J
980 NEXT I
990 REM === Render: clear once, then draw every circle at its new spot ===
1000 if xx$ <> "y" then cls
1010 locate 2,1
1020 textsize 15
1030 print using "###";n
1040 FOR I = 1 TO N
1050 rem if xx$ <> "y" then circle (cxo(i),cyo(i)),r,0
1060 if x$ = "y" then paint (cxo(i),cyo(i)),0
1070 CIRCLE (CX(I),CY(I)),R,CL(I)
1080 if x$ = "y" then paint (cx(i),cy(i)),cl(i)
1090 NEXT I
1100 REM -- Loop back for the next frame --
1110 sleep .007
1120 GOTO 330
